#ifndef pindakaas_h
#define pindakaas_h

/* Warning, this file is autogenerated by cbindgen. Don't modify this manually. */

#include <stdint.h>

typedef enum Comparator {
  LessEq,
  Equal,
  GreaterEq,
} Comparator;

/**
 * The type used to represent Literals in the C Pindakaas library
 */
typedef int32_t Lit;

/**
 * Callback type used when a clause is emitted by the encoder.
 *
 * The first argument will always be the `db` pointer given to the encoding function. The second
 * argument is the pointer to the start of the "slice" of literals that form the clause. The third
 * and final argument gives the number of literals in the clause. The callback function can return
 * `false` to signal when the problem is proven now be unsatisfiable, or `true` otherwise.
 *
 * # Safety
 * The clause given to the callback exists only in temporary memory. If the clause is later
 * used in the same form, then it MUST be copied to persistent memory.
 */
typedef bool (*AddClauseCB)(void*, const Lit*, size_t);

/**
 * Callback type used when a new, unused, Boolean Literal must be created for an encoding.
 *
 * The first argument will always be the `db` pointer given to the encoding function. The return
 * type should be a `Lit` reprenting an unused Boolean Literal.
 */
typedef Lit (*NewVarCB)(void*);

/**
 * The type used to represent Coefficients in the C Pindakaas library
 */
typedef int32_t Coeff;

/**
 * Encodes a Boolean linear expressions into Boolean clauses. TODO: ...
 *
 * # Safety
 * This function depends on receiving valid pointers to arrays of coefficients and literals, and
 * their correct length.
 */
bool encode_bool_lin(void *db,
                     AddClauseCB add_clause_cb,
                     NewVarCB new_var_cb,
                     const Coeff *coeff,
                     size_t coeff_len,
                     const Lit *lit,
                     size_t lit_len,
                     enum Comparator cmp,
                     Coeff _k);

#endif /* pindakaas_h */
