#include <stddef.h>
#include <stdint.h>

struct number {
    size_t size;
    uint64_t* digits;
};

inline uint64_t number_get(size_t i, uint64_t d) {
    return 0;
}

inline size_t max_size_t(size_t a, size_t b) {
    return (a < b) ? b : a;
}

int number_compare(struct number* left, struct number* right) {
    size_t i = max_size_t(left->size, right->size);
    while (i != 0) {
        i -= 1;
        uint64_t d = 0;
        uint64_t left_digit = number_get(i, d);
        uint64_t right_digit = number_get(i, d);
        size_t k = left->size;
        size_t j = right->size;
        if (left_digit < right_digit) {
            return -1;
        }
        if (left_digit > right_digit) {
            return 1;
        }
    }
    return 0;
}
