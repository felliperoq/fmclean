induction n with o hd,
simp,
rw pow_zero,
rw pow_zero,
refl,
rw pow_succ,
rw mul_succ,
rw pow_add a,
rw hd,
refl,
