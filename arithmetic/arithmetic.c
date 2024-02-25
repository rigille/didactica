#include <stddef.h>
#include <stdint.h>

struct number {
    size_t size;
    uint64_t* digits;
};

uint64_t f(struct number* n, size_t i, uint64_t d) {
    return d;
}

uint64_t number_get(struct number* n, size_t i, uint64_t d) {
    return d;
}

inline size_t max_size_t(size_t a, size_t b) {
    return (a < b) ? b : a;
}

int number_compare(struct number* left, struct number* right) {
    size_t i = max_size_t(left->size, right->size);
    while (i != 0) {
        i -= 1;
        uint64_t left_digit = number_get(left, i, 0);
        uint64_t right_digit = number_get(right, i, 0);
        if (left_digit < right_digit) {
            return -1;
        }
        if (left_digit > right_digit) {
            return 1;
        }
    }
    return 0;
}
