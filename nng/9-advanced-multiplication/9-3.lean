split,
intro P,
have Q := eq_zero_or_eq_zero_of_mul_eq_zero a b,
exact Q P,
intro P,
cases P,
rw P,
rw zero_mul,
refl,
rw P,
rw mul_zero,
refl,