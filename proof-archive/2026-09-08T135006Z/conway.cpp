#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>

// Exact sumset computation. Coefficients count ordered representations and
// remain below the NTT modulus, so no floating-point threshold is involved.
constexpr uint64_t MOD = 2013265921, ROOT = 31;
uint64_t power(uint64_t a, uint64_t n) {
    uint64_t r = 1;
    for (; n; n >>= 1, a = a * a % MOD) if (n & 1) r = r * a % MOD;
    return r;
}
void ntt(std::vector<uint32_t>& a, bool inverse) {
    size_t n = a.size();
    for (size_t i = 1, j = 0; i < n; ++i) {
        size_t bit = n >> 1;
        for (; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) std::swap(a[i], a[j]);
    }
    for (size_t len = 2; len <= n; len <<= 1) {
        uint64_t root = power(ROOT, (MOD - 1) / len);
        if (inverse) root = power(root, MOD - 2);
        for (size_t start = 0; start < n; start += len) {
            uint64_t w = 1;
            for (size_t j = 0; j < len / 2; ++j) {
                uint64_t u = a[start + j], v = a[start + j + len / 2] * w % MOD;
                a[start + j] = (u + v) % MOD;
                a[start + j + len / 2] = (u + MOD - v) % MOD;
                w = w * root % MOD;
            }
        }
    }
    if (inverse) {
        uint64_t scale = power(n, MOD - 2);
        for (auto& x : a) x = x * scale % MOD;
    }
}
int main(int argc, char** argv) {
    int rounds = argc > 1 ? std::atoi(argv[1]) : 32;
    uint64_t f0 = 1, f1 = 2;
    for (int n = 1; n < rounds; ++n) { uint64_t f2 = f0 + f1; f0 = f1; f1 = f2; }
    uint64_t limit = 2 * f1;
    if (limit >= MOD || limit >= (1u << 27)) return 2;
    std::vector<uint32_t> spf(limit + 1);
    for (uint32_t p = 2; p <= limit; ++p) if (!spf[p]) {
        spf[p] = p;
        if (uint64_t(p) * p <= limit)
            for (uint64_t k = uint64_t(p) * p; k <= limit; k += p) if (!spf[k]) spf[k] = p;
    }
    std::vector<uint8_t> set(2, 0); set[1] = 1;
    uint64_t prev_count = 1, prev_max = 1;
    std::cout << "n size max even_max core ratio core_over_prev_max holes_below_prev_max missing_primes first_missing_prime\n";
    for (int n = 0; n <= rounds; ++n) {
        size_t m = set.size() - 1, core = 0, even = 0, count = 0, holes = 0, prime_holes = 0, first_prime_hole = 0;
        while (core + 1 <= m && set[core + 1]) ++core;
        for (size_t k = 1; k <= m; ++k) {
            count += set[k];
            if (set[k] && k % 2 == 0) even = k;
            if (k <= prev_max && !set[k]) ++holes;
            if (k >= 2 && spf[k] == k && !set[k]) {
                ++prime_holes;
                if (!first_prime_hole) first_prime_hole = k;
            }
        }
        std::cout << n << ' ' << count << ' ' << m << ' ' << even << ' ' << core << ' '
                  << std::setprecision(12) << double(count) / prev_count << ' '
                  << double(core) / prev_max << ' ' << holes << ' ' << prime_holes << ' ' << first_prime_hole << std::endl;
        if (n == rounds) break;
        size_t sz = 1; while (sz <= 2 * m) sz <<= 1;
        assert(sz <= (1u << 27));
        std::vector<uint32_t> sums(sz);
        std::copy(set.begin(), set.end(), sums.begin());
        ntt(sums, false);
        for (auto& x : sums) x = uint64_t(x) * x % MOD;
        ntt(sums, true);
        if (n <= 14) { // Independent direct convolution at small sizes.
            std::vector<uint32_t> direct(sz);
            for (size_t a = 1; a <= m; ++a) if (set[a])
                for (size_t b = 1; b <= m; ++b) if (set[b]) ++direct[a+b];
            assert(sums == direct);
        }
        set.resize(2 * m + 1);
        for (size_t k = 2; k <= 2 * m; ++k) if (sums[k]) set[spf[k] == k ? k : k / spf[k]] = 1;
        while (!set.back()) set.pop_back();
        prev_count = count; prev_max = m;
    }
}
