#include <bits/stdc++.h>

using std::string;
using i64 = int64_t;
using u64 = uint64_t;
using f128 = long double;
using vec = std::vector<u64>;
using complex = std::complex<f128>;
using cvec = std::vector<complex>;

namespace numbers {
constexpr f128 pi = 3.141592653589793238462643383279L;
constexpr complex ipi = {0, pi};
} // namespace numbers

namespace utils {
// char utils
static constexpr bool is_digit(const char c) {
    return c >= '0' && c <= '9';
}
static constexpr bool is_space(const char c) {
    return c == ' ' || c == '\t' || c == '\n';
}
static constexpr bool is_splitter(const char c) {
    return c == '\'' || c == '_';
}
static constexpr bool is_left_bracket(const char c) {
    return c == '(' || c == '[' || c == '{';
}
static constexpr bool is_right_bracket(const char c) {
    return c == ')' || c == ']' || c == '}';
}

// math utils
template <typename num>
static constexpr num pow(num x, u64 n) {
    num r = 1;
    while (n) {
        if (n & 1) {
            r *= x;
        }
        x *= x, n >>= 1;
    }
    return r;
}
static constexpr u64 powm(u64 x, u64 n, u64 m) {
    u64 r = 1;
    while (n) {
        if (n & 1) {
            r = r * x % m;
        }
        x = x * x % m, n >>= 1;
    }
    return r;
}

static constexpr u64 to2pow(u64 x) {
    return x != 1 && __builtin_popcountll(x) == 1
               ? x
               : 1 << (64 - __builtin_clzll(x));
}

void division(std::vector<complex> &f) {
    int n = f.size();
    auto r = vec(n);
    for (int i = 1; i < n; ++i) {
        r[i] = ((r[i >> 1] >> 1) | (n >> (i & 1))) & ~n;
    }
    for (int i = 1; i < n; ++i) {
        if (i < r[i]) {
            std::swap(f[i], f[r[i]]);
        }
    }
}

template <bool inv>
void FFT(std::vector<complex> &f) {
    division(f);
    int n = f.size();
    for (int now_n = 1; now_n < n; now_n <<= 1) {
        complex omega_n = std::exp(numbers::ipi / (f128)now_n);
        if constexpr (inv)
            omega_n = std::conj(omega_n);
        for (int i = 0; i < n; i += (now_n << 1)) {
            complex omega = 1;
            for (int j = 0; j < now_n; ++j, omega *= omega_n) {
                complex f_1 = f[i + j], f_2 = f[i + j + now_n];
                f[i + j] = f_1 + omega * f_2;
                f[i + j + now_n] = f_1 - omega * f_2;
            }
        }
    }
    if constexpr (inv) {
        std::transform(f.begin(), f.end(), f.begin(),
                       [&](const complex &x) { return x / (f128)n; });
    }
}

template <u64 BASE>
struct numset : public vec {
    using vec::vector;

    numset &fit() noexcept {
        while (size() > 1 && back() == 0) {
            pop_back();
        }
        return *this;
    }

    bool operator>(const numset &other) const {
        auto &self = *this;
        if (size() != other.size()) {
            return size() > other.size();
        }
        for (int i = size() - 1; i >= 0; --i) {
            if (self[i] != other[i]) {
                return self[i] > other[i];
            }
        }
        return false;
    }

    numset &operator+=(const numset &other) {
        auto &self = *this;
        resize(std::max(size(), other.size()) + 1);
        for (int i = 0; i < (signed)other.size(); ++i) {
            self[i] += other[i];
            if (self[i] >= BASE) {
                self[i] -= BASE, self[i + 1] += 1;
            }
        }
        return fit();
    }
    numset &operator-=(const numset &other) {
        auto &self = *this;
        for (int i = 0; i < (signed)other.size(); ++i) {
            if (self[i] < other[i]) {
                self[i] += BASE, self[i + 1] -= 1;
            }
            self[i] -= other[i];
        }
        return fit();
    }
    bool is_zero() const {
        return size() == 1 && back() == 0;
    }
};
} // namespace utils

struct HInt {
    HInt() noexcept : sign(false), value(1, 0) {
    }
    HInt(const string &value) : sign(false) {
        this->value.resize(ceil(value.size() / (float)WIDTH));
        for (int i = 0; i < (signed)this->value.size(); ++i) {
            for (int j = std::max<i64>(value.size() - (i + 1) * WIDTH, 0);
                 j <= (signed)value.size() - i * WIDTH - 1; ++j) {
                this->value[i] *= 10, this->value[i] += value[j] - '0';
            }
        }
    }
    HInt(HInt &&other) noexcept
        : sign(other.sign), value(std::move(other.value)) {
    }
    HInt &operator=(HInt &&other) noexcept {
        if (this != &other) {
            sign = other.sign;
            value = std::move(other.value);
        }
        return *this;
    }

    bool operator>(const HInt &other) const {
        if (sign != other.sign) {
            return sign;
        }
        return sign ^ (value > other.value);
    }

    HInt &operator+=(const HInt &other) {
        if (sign == other.sign) {
            value += other.value;
        } else {
            if (value > other.value) {
                value -= other.value;
            } else {
                auto tmp = other.value;
                tmp -= value;
                value = std::move(tmp);
                sign = !sign;
            }
        }
        return fit();
    }
    HInt &operator-=(const HInt &other) {
        if (sign == other.sign) {
            if (value > other.value) {
                value -= other.value;
            } else {
                auto tmp = other.value;
                tmp -= value;
                value = std::move(tmp);
                sign = !sign;
            }
        } else {
            value += other.value;
        }
        return fit();
    }

    HInt &operator*=(const HInt &other) {
        auto f = cvec(value.begin(), value.end());
        const u64 n =
            utils::to2pow(2 * std::max(value.size(), other.value.size()));
        f.resize(n);
        std::transform(
            other.value.begin(), other.value.end(), f.begin(), f.begin(),
            [&](u64 x, const complex &y) { return complex(y.real(), x); });

        utils::FFT<false>(f);
        std::transform(f.begin(), f.end(), f.begin(),
                       [&](const complex &x) { return x * x; });
        utils::FFT<true>(f);
        std::transform(f.begin(), f.end(), f.begin(), [&](const complex &x) {
            return complex(x.imag() / 2, 0);
        });

        value.resize(n);
        std::transform(
            f.begin(), f.end(), value.begin(),
            [&](const complex &x) -> u64 { return std::roundl(x.real()); });
        for (int i = 0; i < n; ++i) {
            if (value[i] >= BASE) {
                value[i + 1] += value[i] / BASE;
                value[i] %= BASE;
            }
        }

        sign ^= other.sign;
        return fit();
    }

    friend std::istream &operator>>(std::istream &is, HInt &x) {
        string s;
        is >> s;
        x = HInt(s);
        return is;
    }
    friend std::ostream &operator<<(std::ostream &os, const HInt &x) {
        if (x.sign) {
            os << '-';
        }
        os << x.value.back();
        for (auto i = x.value.rbegin() + 1; i != x.value.rend(); ++i) {
            os << std::setw(WIDTH) << std::setfill('0') << *i;
        }
        return os;
    }

  protected:
    static constexpr u64 WIDTH = 4;
    static constexpr u64 BASE = utils::pow<u64>(10, WIDTH);

  private:
    bool sign;
    utils::numset<BASE> value;

    HInt &fit() {
        value.fit();
        if (value.is_zero()) {
            sign = false;
        }
        return *this;
    }
};

struct AST {
    struct Node {
        union {
            std::unique_ptr<char> operation;
            std::unique_ptr<HInt> number;
        };
        std::vector<Node *> children;
    } *root;

    AST(const string &code) {
        std::stack<Node *> stack;
        std::stack<char> operation;

        const auto append = [&stack, &operation](Node *node) {
            if (stack.empty()) {
                stack.push(node);
            } else {
                stack.top()->children.push_back(node);
            }
        };

        for (auto i = code.begin(); i != code.end(); ++i) {
            if (utils::is_space(*i) || *i == '\\') {
                continue;
            } else if (utils::is_digit(*i)) {
                string number;
                while (i != code.end() &&
                       (utils::is_digit(*i) || utils::is_splitter(*i))) {
                    if (!utils::is_splitter(*i)) {
                        number += *i;
                    }
                    ++i;
                }
            } else {
                switch (*i) {
                case '(':
                case '[':
                case '{': {
                    operation.push(*i);
                } break;
                case ')':
                case ']':
                case '}': {
                } break;
                }
            }
        }
    }
};

int main() {
    return 0;
}
