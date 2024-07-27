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

#ifdef __GNUC__ // gcc and clang use a builtin
                // TODO: add that ugly implementation for gcc < 14
inline uint64_t add_with_carry(
    uint64_t left_digit, uint64_t right_digit,
    uint64_t carry_in, uint64_t* carry_out
) {
    return __builtin_addcl(
        left_digit, right_digit,
        carry_in, carry_out
    );
}
#else // Other compilers will have this portable, likely
      // inefficient implementation. I don't say
      // it's for sure inefficient because Clang would
      // optimize this just as well as the builtin.
      // Compcert would benefit from this intrinsic
inline uint64_t add_with_carry(
    uint64_t left_digit, uint64_t right_digit,
    uint64_t carry_in, uint64_t* carry_out
) {
    uint64_t temporary = carry_in + left_digit;
    uint64_t result = temporary + right_digit;
    *carry_out =
        // I'm casting to unsigneds because I don't feel
        // like proving this addition doesn't overflow
        (uint64_t)(temporary < carry_in) +
        (uint64_t)(result < right_digit);
    return result;
}
#endif

void number_add_inner(
    struct number* left,
    struct number* right,
    struct number* target
) {
    size_t i = max_size_t(left->size, right->size);
    uint64_t carry = 0;
    for (size_t j = 0; j < i; j++) {
        uint64_t left_digit = number_get(left, j);
        uint64_t right_digit = number_get(right, j);
        uint64_t result = add_with_carry(
                left_digit, right_digit,
                carry, &carry
        );
        target->digits[j] = result;
    }
}

void number_multiply_inner(
    struct number* left,
    struct number* right,
    struct number* target
) {
    uint32_t* left_digits = (uint32_t*)left->digits;
    uint32_t* right_digits = (uint32_t*)right->digits;
    uint32_t* target_digits = (uint32_t*)target->digits;
    for (size_t i = 0; i < 2*left->size; i++) {
        uint64_t left_digit = (uint64_t)left_digits[i];
        uint64_t result = 0;
        for (size_t j = 0; j < 2*right->size; j++) {
            uint64_t right_digit = (uint64_t)right_digits[i];
            result += (uint64_t)target_digits[i+j];
            result += left_digit*right_digit;
            target_digits[i+j] = (uint32_t)result;
            result = result >> 32;
        }
    }
}
