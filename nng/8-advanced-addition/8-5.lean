intro c,
induction t with u hd,
exact c,
rw add_succ a at c,
rw add_succ b at c,
have d := succ_inj c,
have e := hd(d),
exact e,