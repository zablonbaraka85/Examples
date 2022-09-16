-------------------------- MODULE DyadicRationals ---------------------------
\* https://en.wikipedia.org/wiki/Dyadic_rational
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSetsExt
LOCAL INSTANCE TLC

LOCAL Divides(p, q) == 
    \E d \in 1..q : q = p * d

LOCAL Divisors(q) ==
    {d \in 1..q : Divides(d, q)}

LOCAL GCD(n, m) ==
    Max(Divisors(n) \cap Divisors(m))

------------------------------------------------------------------------------

LOCAL Rational(num, dem) ==
    [num |-> num, dem |-> dem]

LOCAL Reduce(p) ==
    LET gcd == GCD(p.num, p.dem)
    IN  IF gcd = 1 THEN p
        ELSE Rational(p.num \div gcd, p.dem \div gcd)

IsDyadicRational(r) ==
    \E i \in 0..r.dem: 2^i = r.dem 

Zero == Rational(0,1)

One == Rational(1,1)

Add(p, q) ==
    IF p = Zero THEN q ELSE
    LET lcn == Max({p.dem, q.dem}) \* shortcut because dyadic!
        qq == Rational(q.num * (lcn \div q.dem), q.dem * (lcn \div q.dem))
        pp == Rational(p.num * (lcn \div p.dem), p.dem * (lcn \div p.dem))
    IN Reduce(Rational(qq.num + pp.num, lcn))

Half(p) ==
    Reduce(Rational(p.num, p.dem * 2))

PrettyPrint(p) ==
    IF p = Zero THEN "0" ELSE
    IF p = One THEN "1" ELSE
    ToString(p.num) \o "/" \o ToString(p.dem)

===============================================================================
\* Modification History
\* Last modified Mon Dec 27 17:52:54 PST 2021 by Markus Kuppe
\* Created Sun Dec 26 01:36:40 PDT 2021 by Markus Kuppe