:- use_package([assertions]).

:- doc(filetype, documentation).

:- doc(title,"Improving Analysis Using Trust Assertions").

:- doc(module,"
This section describes the use of trust assertions for improving (abstract
interpretation based) top-down analyses. Trust assertions are (user given)
assertions that do hold of the program. Therefore, analysis can take 
advantage of them to improve the information inferred.

A trust assertion for a given predicate will be denoted @tt{C} @result @tt{S},
where @tt{C} is a call pattern and @tt{S} a success pattern. Trust assertions
for a given predicate are considered closed, that is, the set of call patterns
covers all possible calls to the predicate.@footnote{Reconsider this: It is not
true for trust assertions inferred during inter-modular analysis. It may not be
convenient, either, when having true/trust and check assertions intermixed.}

In the following, @tt{L} @result @tt{L'} will denote the abstract pattern
inferred for a given predicate call by the analysis which is going to be
improved with trust assertions. In the absence of the predicate, the success
pattern cannot be inferred: however, it can be approximated a priori by the
downwards closed information in the call pattern. Thus, if this is the case,
@tt{L' = L*}, where @tt{L*} denotes the downwards closure restriction of @tt{L}
(i. e., the restriction of @tt{L} to only its downwards closed information).

@section{Complementation of Trust Assertions}

Programmers are lazy writing trust assertions. This is not to blame them: it
is just a matter of fact. They try to write as less as possible, and therefore
make certain (justified) assumptions when writing assertions. Because of this,
trust assertions need to be complemented in order to have as much information
as possible available to the analysis.

One thing that programmers usually do is to write things like:

@tt{ground(X)} @result @tt{var(Y)}

where it is obvious that @tt{ground(X)} does also hold on success. In order to
deal with this case, trust assertions of the form @tt{C} @result @tt{S} are
replaced by @tt{C} @result @tt{S'}, where:

@tt{S' = C* meet S}

Another usual assumption in writing assertions is to say things once and for
all. For example, programmers will probable write:

@tt{true} @result @tt{ground(X)}@p
@tt{var(X)} @result @tt{var(Y)}

where it is obvious that @tt{ground(X)} does also hold on success in the second
case. In order to deal with this case, trust assertions of the form @tt{C}@result
@tt{S'} are replaced by @tt{C}@result @tt{S''} where:

@tt{S'' = S' meet (meet S'_i)}

being @tt{C_i}@result @tt{S'_i} a trust assertion such that @tt{C_i >= C}.

Now we are in a position to take full advantage of all the information given
in trust assertions.

@section{Using Trust Assertions}

Given abstract pattern @tt{L}@result @tt{L'}, the success pattern can be
improved by using the available trust assertions. The resulting success pattern
is denoted @tt{L_trust}. For better precision the most concrete applicable trust
assertion should be used. Consider the set:

@tt{St = @{S''_i | C_i >= L and not exists j =/= i . C_j =< C_i @}}

then:

@tt{L_trust = L' meet (union St)}

However, @tt{St} might be empty. In this case, no trust assertion is guaranteed to hold.
But the call pattern inferred might be an over-approximation of the call patterns
of some trust assertions. And one of them must hold (since the trust assertions are
supposed to be closed). Thus, in this case @tt{St} is defined as:

@tt{St = @{S''_i | C_i =< L and not exists j =/= i . C_j >= C_i | @}}

Nonetheless, it might also be the case that this set is empty. Then, since the trust
assertions are supposed to be closed, this is an error: the inferred call pattern
does not cover the possible calls.

But, in order to guarantee this error, all trust assertions should be applicable to
the analysis domain (all call patterns should be fully abstractable in that domain).
If this is not the case, a default success pattern can be used by defining:
@footnote{In contrast to the above, here @tt{St} must include all trust assertions,
whether or not applicable to the domain. This implies that the second @tt{St} above
might be incorrect!}

@tt{St = @{S''_i | exists i@}}
 ").
