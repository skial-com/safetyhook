#include "safetyhook/common.hpp"

#if SAFETYHOOK_OS_LINUX

#include <algorithm>
#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <string>

#include <fcntl.h>

#include <sys/mman.h>
#include <unistd.h>

#include "safetyhook/utility.hpp"

#include "safetyhook/os.hpp"

#ifndef MAP_FIXED_NOREPLACE
#define MAP_FIXED_NOREPLACE 0x100000
#endif

namespace safetyhook {
std::expected<uint8_t*, OsError> vm_allocate(uint8_t* address, size_t size, VmAccess access) {
    int prot = 0;
    int flags = MAP_PRIVATE | MAP_ANONYMOUS;

    // Like VirtualAlloc, fail instead of placing the memory somewhere else when the address is taken.
    if (address != nullptr) {
        flags |= MAP_FIXED_NOREPLACE;
    }

    if (access == VM_ACCESS_R) {
        prot = PROT_READ;
    } else if (access == VM_ACCESS_RW) {
        prot = PROT_READ | PROT_WRITE;
    } else if (access == VM_ACCESS_RX) {
        prot = PROT_READ | PROT_EXEC;
    } else if (access == VM_ACCESS_RWX) {
        prot = PROT_READ | PROT_WRITE | PROT_EXEC;
    } else {
        return tl::unexpected{OsError::FAILED_TO_ALLOCATE};
    }

    auto* result = mmap(address, size, prot, flags, -1, 0);

    if (result == MAP_FAILED) {
        return tl::unexpected{OsError::FAILED_TO_ALLOCATE};
    }

    // Kernels before 4.17 ignore MAP_FIXED_NOREPLACE and treat the address as a hint.
    if (address != nullptr && result != address) {
        munmap(result, size);
        return tl::unexpected{OsError::FAILED_TO_ALLOCATE};
    }

    return static_cast<uint8_t*>(result);
}

void vm_free(uint8_t* address) {
    munmap(address, 0);
}

std::expected<uint32_t, OsError> vm_protect(uint8_t* address, size_t size, VmAccess access) {
    int prot = 0;

    if (access == VM_ACCESS_R) {
        prot = PROT_READ;
    } else if (access == VM_ACCESS_RW) {
        prot = PROT_READ | PROT_WRITE;
    } else if (access == VM_ACCESS_RX) {
        prot = PROT_READ | PROT_EXEC;
    } else if (access == VM_ACCESS_RWX) {
        prot = PROT_READ | PROT_WRITE | PROT_EXEC;
    } else {
        return tl::unexpected{OsError::FAILED_TO_PROTECT};
    }

    return vm_protect(address, size, prot);
}

std::expected<uint32_t, OsError> vm_protect(uint8_t* address, size_t size, uint32_t protect) {
    auto mbi = vm_query(address);

    if (!mbi.has_value()) {
        return tl::unexpected{OsError::FAILED_TO_PROTECT};
    }

    uint32_t old_protect = 0;

    if (mbi->access.read) {
        old_protect |= PROT_READ;
    }

    if (mbi->access.write) {
        old_protect |= PROT_WRITE;
    }

    if (mbi->access.execute) {
        old_protect |= PROT_EXEC;
    }

    auto* addr = align_down(address, static_cast<size_t>(sysconf(_SC_PAGESIZE)));

    if (mprotect(addr, size, static_cast<int>(protect)) == -1) {
        return tl::unexpected{OsError::FAILED_TO_PROTECT};
    }

    return old_protect;
}

namespace {
// Reads the mapped regions from /proc/self/maps in one pass. Lines are "start-end perms offset dev inode path".
bool read_maps(std::vector<VmBasicInfo>& regions) {
    auto fd = open("/proc/self/maps", O_RDONLY | O_CLOEXEC);

    if (fd == -1) {
        return false;
    }

    std::string buf;
    char chunk[16384];

    for (;;) {
        auto n = read(fd, chunk, sizeof(chunk));

        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }

            close(fd);
            return false;
        }

        if (n == 0) {
            break;
        }

        buf.append(chunk, static_cast<size_t>(n));
    }

    close(fd);

    regions.clear();

    const char* p = buf.c_str();

    while (*p != '\0') {
        char* e{};
        auto start = strtoul(p, &e, 16);

        if (e == p || *e != '-') {
            break;
        }

        p = e + 1;
        auto end = strtoul(p, &e, 16);

        if (e == p || *e != ' ' || e[1] == '\0' || e[2] == '\0' || e[3] == '\0') {
            break;
        }

        VmBasicInfo info{};
        info.address = reinterpret_cast<uint8_t*>(start);
        info.size = end - start;
        info.access = VmAccess(e[1] == 'r', e[2] == 'w', e[3] == 'x');
        info.is_free = false;
        regions.push_back(info);

        p = strchr(e, '\n');

        if (p == nullptr) {
            break;
        }

        ++p;
    }

    return true;
}

// Same answer as walking the maps in order: the mapping that contains address, or the unmapped gap before the
// first mapping above it (gaps start no lower than system_info().min_address).
std::expected<VmBasicInfo, OsError> query_regions(const std::vector<VmBasicInfo>& regions, uint8_t* address) {
    auto it = std::upper_bound(regions.begin(), regions.end(), address,
        [](uint8_t* addr, const VmBasicInfo& r) { return addr < r.address + r.size; });

    if (it == regions.end()) {
        return tl::unexpected{OsError::FAILED_TO_QUERY};
    }

    if (address >= it->address) {
        return *it;
    }

    auto* last_end = it == regions.begin() ? system_info().min_address : (it - 1)->address + (it - 1)->size;

    if (last_end < it->address && address >= last_end) {
        VmBasicInfo info{};
        info.address = last_end;
        info.size = static_cast<size_t>(it->address - last_end);
        info.access = VmAccess();
        info.is_free = true;
        return info;
    }

    return tl::unexpected{OsError::FAILED_TO_QUERY};
}
} // namespace

std::expected<VmBasicInfo, OsError> vm_query(uint8_t* address) {
    std::vector<VmBasicInfo> regions;

    if (!read_maps(regions)) {
        return tl::unexpected{OsError::FAILED_TO_QUERY};
    }

    return query_regions(regions, address);
}

VmSnapshot::VmSnapshot() {
    m_valid = read_maps(m_regions);
}

std::expected<VmBasicInfo, OsError> VmSnapshot::query(uint8_t* address) const {
    if (!m_valid) {
        return tl::unexpected{OsError::FAILED_TO_QUERY};
    }

    return query_regions(m_regions, address);
}

bool vm_is_readable(uint8_t* address, [[maybe_unused]] size_t size) {
    return vm_query(address).value_or(VmBasicInfo{}).access.read;
}

bool vm_is_writable(uint8_t* address, [[maybe_unused]] size_t size) {
    return vm_query(address).value_or(VmBasicInfo{}).access.write;
}

bool vm_is_executable(uint8_t* address) {
    return vm_query(address).value_or(VmBasicInfo{}).access.execute;
}

SystemInfo system_info() {
    auto page_size = static_cast<uint32_t>(sysconf(_SC_PAGESIZE));

    SystemInfo info;
    info.page_size = page_size;
    info.allocation_granularity = page_size;
    info.min_address = reinterpret_cast<uint8_t*>(0x10000);
    info.max_address = reinterpret_cast<uint8_t*>(1ull << 47);
    return info;
}

void trap_threads([[maybe_unused]] uint8_t* from, [[maybe_unused]] uint8_t* to, [[maybe_unused]] size_t len,
    const std::function<void()>& run_fn) {
    auto from_protect = vm_protect(from, len, VM_ACCESS_RWX).value_or(0);
    auto to_protect = vm_protect(to, len, VM_ACCESS_RWX).value_or(0);
    run_fn();
    vm_protect(to, len, to_protect);
    vm_protect(from, len, from_protect);
}

void fix_ip([[maybe_unused]] ThreadContext ctx, [[maybe_unused]] uint8_t* old_ip, [[maybe_unused]] uint8_t* new_ip) {
}

} // namespace safetyhook

#endif