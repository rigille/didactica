#include <stddef.h>
#include <stdint.h>

struct number {
    size_t size;
    uint64_t* digits;
};

int number_compare(struct number* left, struct number* right) {
    size_t i = (left->size < right->size) ? right->size : left->size;
    while (i != 0) {
        i -= 1;
        uint64_t left_digit = (i < left->size) ? left->digits[i] : 0;
        uint64_t right_digit = (i < right->size) ? right->digits[i] : 0;
        if (left_digit < right_digit) {
            return -1;
        }
        if (left_digit > right_digit) {
            return 1;
        }
    }
    return 0;
}
