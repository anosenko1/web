#include <stdio.h>
#include <inttypes.h>
#include <string.h>
#include <stdlib.h>
#include "constants.h"

#define BLOCK_SIZE 16 // bytes

typedef uint8_t v128[BLOCK_SIZE]; // 8 bit * 16 = 128 bit = 16 bytes

/* char string to hex 16 Byte array */
void placeStringToBlock(char *str, uint8_t *block);
int charArrayHexToInt(char *input);
int charHexToInt(char input);

/* mul over x^8 + x^7 + x^6 + x + 1. */
uint8_t mul(uint8_t a, uint8_t b) {
    uint8_t c = 0;
    uint8_t hi_bit;
    for (int i = 0; i < 8; i++) {
        if (b & 1)
            c ^= a;
        hi_bit = a & 0x80;
        a <<= 1;
        if (hi_bit)
            a ^= 0xc3; // Полином x^8 + x^7 + x^6 + x + 1
        b >>= 1;
    }
    return c;
}

uint8_t **consts;      // итерационные константы
v128 iter_key[10];     // Итерационные ключи шифрования

void X(const uint8_t *a, const uint8_t *b, uint8_t *result);
void S(const uint8_t *input, uint8_t *result);
void R(uint8_t *target);
void L(const uint8_t *input, uint8_t *result);
void inverse_S(const uint8_t *input, uint8_t *result);
void inverse_R(uint8_t *target);
void inverse_L(const uint8_t *input, uint8_t *result);
void F(const uint8_t *in_key_1, const uint8_t *in_key_2, uint8_t *out_key_1, uint8_t *out_key_2, uint8_t *iter_const);

void init_iter_consts();
void expand_keys(const uint8_t *key1, const uint8_t *key2);
void encrypt(const uint8_t *input, uint8_t *result);
void decrypt(const uint8_t *input, uint8_t *result);

void test_start();
int test_S();
int test_R();
int test_L();
int test_S_for(char *s, char *answer);
int test_R_for(char *s, char *answer);
int test_L_for(char *s, char *answer);
int test_backS_for(char *s, char *answer);
int test_backR_for(char *s, char *answer);
int test_backL_for(char *s, char *answer);
int test_encrypt_decrypt();


/*  X: V128 -> V128: X(k,a) = k ⊕ a */
void X(const uint8_t *a, const uint8_t *b, uint8_t *result) {
    for (int i = 0; i < BLOCK_SIZE; i++)
        result[i] = a[i] ^ b[i];
}

/*  S: V128 → V128 S(a) = S(a15||…||a0) = π(a15)||…||π(a0),
    где a = a15||…||a0 ∈ V128, ai ∈ V8, i = 0, 1, …, 15; */
void S(const uint8_t *input, uint8_t *result) {
    for (int i = 0; i < BLOCK_SIZE; i++)
        result[i] = Pi[input[i]];
}

void inverse_S(const uint8_t *input, uint8_t *result) {
    for (int i = 0; i < BLOCK_SIZE; i++)
        result[i] = inverse_Pi[input[i]];
}

// R: V128 → V128 R(a) = R(a15||…||a0) = ℓ(a15, …, a0)||a15||…||a1,
// где a = a15||…||a0 ∈ V128, ai ∈ V8, i = 0, 1, …, 15;
void R(uint8_t *target) {
    uint8_t temp_byte = 0;
    for (int i = 0; i < BLOCK_SIZE; i++)
        temp_byte ^= mul(target[i], R_coefficient_array[i]); // TODO: оптимизировать!
    for (int i = BLOCK_SIZE - 1; i > 0; i--)
        target[i] = target[i - 1];
    *target = temp_byte;
}

void inverse_R(uint8_t *target) {
    uint8_t temp_byte = *target;
    for (int i = 0; i < BLOCK_SIZE - 1; i++)
        target[i] = target[i + 1];
    target[15] = temp_byte;
    // мб вынести в отдельную
    unsigned short result = 0;
    for (int i = 0; i < BLOCK_SIZE; i++) {
        result ^= mul(target[i], R_coefficient_array[i]);
    }
    target[15] = result;
}

// L: V128 → V128 L(a) = R16(a),
// где a ∈ V128;
void L(const uint8_t *input, uint8_t *result) {
    v128 temp_vec;
    memcpy(temp_vec, input, BLOCK_SIZE);
    for (int i = 0; i < 16; i++)
        R(temp_vec);
    memcpy(result, temp_vec, BLOCK_SIZE);
}

void inverse_L(const uint8_t *input, uint8_t *result) {
    v128 internal;
    memcpy(internal, input, BLOCK_SIZE);
    for (int i = 0; i < 16; i++) {
        inverse_R(internal);
    }
    memcpy(result, internal, BLOCK_SIZE);
}

// free consts, consts[i]
void init_iter_consts() {  // TODO: оптимизировать!
    consts = (uint8_t **) calloc(32, sizeof(uint8_t *));
    for (int i = 0; i < 32; ++i) {
        consts[i] = (uint8_t *) calloc(16, sizeof(uint8_t));
    }
    uint8_t **it_number = (uint8_t **) calloc(32, sizeof(uint8_t *));
    for (int i = 0; i < 32; ++i) {
        it_number[i] = (uint8_t *) calloc(16, sizeof(uint8_t));
    }
    for (int i = 0; i < 32; ++i) {
        it_number[i][15] = i + 1;
        L(it_number[i], consts[i]);
    }
}

// F [k]: V128 × V128 →V128 × V128F [k](a1, a0) = (LSX[k](a1) ⊕ a0, a1),
// где k, a0, a1 ∈ V128.
void F(const uint8_t *in_key_1, const uint8_t *in_key_2, uint8_t *out_key_1, uint8_t *out_key_2, uint8_t *iter_const) {
    v128 temp_vec;
    memcpy(out_key_2, in_key_1, BLOCK_SIZE);
    X(in_key_1, iter_const, temp_vec);
    S(temp_vec, temp_vec);
    L(temp_vec, temp_vec);
    X(temp_vec, in_key_2, out_key_1);
}

void expand_keys(const uint8_t *key1, const uint8_t *key2) {
    uint8_t key_previous1[64];
    uint8_t key_previous2[64];
    uint8_t key_new1[64];
    uint8_t key_new2[64];

    init_iter_consts();

    memcpy(iter_key[0], key1, 64);
    memcpy(iter_key[1], key2, 64);
    memcpy(key_previous1, key1, 64);
    memcpy(key_previous2, key2, 64);

    for (int i = 0; i < 4; i++) {
        F(key_previous1, key_previous2, key_new1, key_new2, consts[0 + 8 * i]);
        F(key_new1, key_new2, key_previous1, key_previous2, consts[1 + 8 * i]);
        F(key_previous1, key_previous2, key_new1, key_new2, consts[2 + 8 * i]);
        F(key_new1, key_new2, key_previous1, key_previous2, consts[3 + 8 * i]);
        F(key_previous1, key_previous2, key_new1, key_new2, consts[4 + 8 * i]);
        F(key_new1, key_new2, key_previous1, key_previous2, consts[5 + 8 * i]);
        F(key_previous1, key_previous2, key_new1, key_new2, consts[6 + 8 * i]);
        F(key_new1, key_new2, key_previous1, key_previous2, consts[7 + 8 * i]);
        memcpy(iter_key[2 * i + 2], key_previous1, 64);
        memcpy(iter_key[2 * i + 3], key_previous2, 64);
    }
}

void encrypt(const uint8_t *input, uint8_t *result) {
    memcpy(result, input, BLOCK_SIZE);
    for (int i = 0; i < 9; i++) {
        X(iter_key[i], result, result);
        S(result, result);
        L(result, result);
    }
    X(result, iter_key[9], result);
}

void decrypt(const uint8_t *input, uint8_t *result) {
    memcpy(result, input, BLOCK_SIZE);
    X(result, iter_key[9], result);
    for (int i = 8; i >= 0; i--) {
        inverse_L(result, result);
        inverse_S(result, result);
        X(iter_key[i], result, result);
    }
}

int main() {

    test_start();

    return 0;
}

#define SUCCESS 1
#define FAIL 0

int test_S_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *result = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    S(input_hex, result);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    printf("\t -S-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", result[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != result[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");

    free(input_hex);
    free(result);
    free(answer_hex);
    return SUCCESS;
}

int test_backS_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *result = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    inverse_S(input_hex, result);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    printf("\t -inverse_S-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", result[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != result[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");

    free(input_hex);
    free(result);
    free(answer_hex);
    return SUCCESS;
}

int test_R_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    R(input_hex);
    printf("\t -R-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != input_hex[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");
    free(input_hex);
    free(answer_hex);
    return SUCCESS;
}

int test_backR_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    inverse_R(input_hex);
    printf("\t -backR-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != input_hex[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");
    free(input_hex);
    free(answer_hex);
    return SUCCESS;
}

int test_L_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *result = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    L(input_hex, result);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    printf("\t -L-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", result[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != result[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");


    free(input_hex);
    free(result);
    free(answer_hex);


    return SUCCESS;
}

int test_backL_for(char *s, char *answer) {
    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *result = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *answer_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock(s, input_hex);
    placeStringToBlock(answer, answer_hex);

    inverse_L(input_hex, result);

    for (int i = 0; i < 16; ++i) printf("%x", input_hex[i]);
    printf("\t -backL-> \t");
    for (int i = 0; i < 16; ++i) printf("%x", result[i]);

    for (int i = 0; i < 16; ++i)
        if (answer_hex[i] != result[i]) {
            printf("\t<- FALSE!");
            return FAIL;
        }
    printf("\t<- TRUE!\n");

    free(input_hex);
    free(result);
    free(answer_hex);
    return SUCCESS;
}

int test_L() {
    printf("Test L started\n");
    if (!test_L_for("64a59400000000000000000000000000", "d456584dd0e3e84cc3166e4b7fa2890d"))
        return FAIL;
    if (!test_L_for("d456584dd0e3e84cc3166e4b7fa2890d", "79d26221b87b584cd42fbc4ffea5de9a"))
        return FAIL;
    if (!test_L_for("79d26221b87b584cd42fbc4ffea5de9a", "0e93691a0cfc60408b7b68f66b513c13"))
        return FAIL;
    if (!test_L_for("0e93691a0cfc60408b7b68f66b513c13", "e6a8094fee0aa204fd97bcb0b44b8580"))
        return FAIL;
    if (!test_backL_for("e6a8094fee0aa204fd97bcb0b44b8580", "0e93691a0cfc60408b7b68f66b513c13"))
        return FAIL;
    if (!test_backL_for("0e93691a0cfc60408b7b68f66b513c13", "79d26221b87b584cd42fbc4ffea5de9a"))
        return FAIL;
    if (!test_backL_for("79d26221b87b584cd42fbc4ffea5de9a", "d456584dd0e3e84cc3166e4b7fa2890d"))
        return FAIL;
    if (!test_backL_for("d456584dd0e3e84cc3166e4b7fa2890d", "64a59400000000000000000000000000"))
        return FAIL;
    return SUCCESS;
}

int test_S() {
    printf("\nTest S started\n");
    if (!test_S_for("ffeeddccbbaa99881122334455667700", "b66cd8887d38e8d77765aeea0c9a7efc"))
        return FAIL;
    if (!test_S_for("b66cd8887d38e8d77765aeea0c9a7efc", "559d8dd7bd06cbfe7e7b262523280d39"))
        return FAIL;
    if (!test_S_for("559d8dd7bd06cbfe7e7b262523280d39", "0c3322fed531e4630d80ef5c5a81c50b"))
        return FAIL;
    if (!test_S_for("0c3322fed531e4630d80ef5c5a81c50b", "23ae65633f842d29c5df529c13f5acda"))
        return FAIL;
    if (!test_backS_for("23ae65633f842d29c5df529c13f5acda", "0c3322fed531e4630d80ef5c5a81c50b"))
        return FAIL;
    if (!test_backS_for("0c3322fed531e4630d80ef5c5a81c50b", "559d8dd7bd06cbfe7e7b262523280d39"))
        return FAIL;
    return SUCCESS;
}

int test_R() {
    printf("Test R started\n");
    if (!test_R_for("00000000000000000000000000000100", "94000000000000000000000000000001"))
        return FAIL;
    if (!test_R_for("94000000000000000000000000000001", "a5940000000000000000000000000000"))
        return FAIL;
    if (!test_R_for("a5940000000000000000000000000000", "64a59400000000000000000000000000"))
        return FAIL;
    if (!test_R_for("64a59400000000000000000000000000", "0d64a594000000000000000000000000"))
        return FAIL;
    if (!test_backR_for("0d64a594000000000000000000000000", "64a59400000000000000000000000000"))
        return FAIL;
    if (!test_backR_for("64a59400000000000000000000000000", "a5940000000000000000000000000000"))
        return FAIL;
    if (!test_backR_for("a5940000000000000000000000000000", "94000000000000000000000000000001"))
        return FAIL;
    if (!test_backR_for("94000000000000000000000000000001", "00000000000000000000000000000100"))
        return FAIL;
    return SUCCESS;
}

int test_encrypt_decrypt(){
    uint8_t *key1 = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock("8899aabbccddeeff0011223344556677", key1);
    uint8_t *key2 = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock("fedcba98765432100123456789abcdef", key2);

    expand_keys(key1, key2);

    free(key1);
    free(key2);

    uint8_t *input_hex = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock("1122334455667700ffeeddccbbaa9988", input_hex);
    uint8_t *output = (uint8_t *) calloc(16, sizeof(uint8_t));
    uint8_t *result = (uint8_t *) calloc(16, sizeof(uint8_t));
    placeStringToBlock("7f679d90bebc24305a468d42b9d4edcd", result);

    encrypt(input_hex, output);
    for (int i = 0; i < 16; ++i)
        if (output[i] != result[i]) {
            printf("FALSE!");
            for (int i1 = 0; i1 < 32; ++i1) {
                free(consts[i1]);
            }
            free(consts);
            free(input_hex);
            free(output);
            free(result);
            return FAIL;
        }
    printf("encrypting - TRUE!\n");

    decrypt(result, output);
    for (int i = 0; i < 16; ++i)
        if (output[i] != input_hex[i]) {
            printf("FALSE!");
            for (int i1 = 0; i1 < 32; ++i1) {
                free(consts[i1]);
            }
            free(consts);
            free(input_hex);
            free(output);
            free(result);
            return FAIL;
        }
    printf("decrypting - TRUE!\n");

    for (int i = 0; i < 32; ++i) {
        free(consts[i]);
    }
    free(consts);
    free(input_hex);
    free(output);
    free(result);

    return SUCCESS;
}

void test_start() {
    test_S() ? printf("Test S passed\n") : printf("\nTest S failed\n");
    test_R() ? printf("Test R passed\n") : printf("\nTest R failed\n");
    test_L() ? printf("Test L passed\n") : printf("\nTest L failed\n");
    test_encrypt_decrypt() ? printf("Test encrypt & decrypt passed\n") : printf("\nTest encrypt & decrypt failed\n");
}

// f -> 15
int charHexToInt(char input) {
    if (input == 'A' || input == 'a') return 10;
    if (input == 'B' || input == 'b') return 11;
    if (input == 'C' || input == 'c') return 12;
    if (input == 'D' || input == 'd') return 13;
    if (input == 'E' || input == 'e') return 14;
    if (input == 'F' || input == 'f') return 15;
    if (input == '9') return 9;
    if (input == '8') return 8;
    if (input == '7') return 7;
    if (input == '6') return 6;
    if (input == '5') return 5;
    if (input == '4') return 4;
    if (input == '3') return 3;
    if (input == '2') return 2;
    if (input == '1') return 1;
    if (input == '0') return 0;
    return -1;
}

// ff -> 255
int charArrayHexToInt(char *input) {
    int term1, term2;
    if ((term1 = charHexToInt(input[1])) == -1) return -1;
    if ((term2 = charHexToInt(input[0])) == -1) return -1;
    return term1 + term2 * 16;
}

// char[32] str -> int hex[16] with bad str check!
void placeStringToBlock(char *str, uint8_t *block) {
    for (int i = 0; i < BLOCK_SIZE; ++i) {
        int hex = charArrayHexToInt(&str[2 * i]);
        if (hex == -1) fprintf(stderr, "Error: bad input string, symbol: %c%c\n", str[2 * i], str[2 * i + 1]);
        block[i] = hex; // int to uint8_t
    }
}

