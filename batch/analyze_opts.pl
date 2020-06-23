% (included file)

domain(eterms).
domain(shfr).

find_set_pp_flags :-
    set_pp_flag(entry_point, calls),
    set_pp_flag(fact_info, on),
    set_pp_flag(multivariant_ctchecks, on),
    set_pp_flag(collapse_ai_vers, off),
    set_pp_flag(use_check_assrt, on).
