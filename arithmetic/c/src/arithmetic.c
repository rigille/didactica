#include <stddef.h>
#include <stdint.h>

struct number {
    size_t size;
    uint64_t* digits;
};

inline uint64_t number_get(struct number* n, size_t i) {
    return (i < n->size) ? n->digits[i] : (uint64_t)0;
}

inline size_t max_size_t(size_t a, size_t b) {
    return (a < b) ? b : a;
}

int number_compare(struct number* left, struct number* right) {
    size_t i = max_size_t(left->size, right->size);
    while (i != 0) {
        i -= 1;
        uint64_t left_digit = number_get(left, i);
        uint64_t right_digit = number_get(right, i);
        if (left_digit < right_digit) {
            return -1;
        }
        if (right_digit < left_digit) {
            return 1;
        }
    }
    return 0;
}
