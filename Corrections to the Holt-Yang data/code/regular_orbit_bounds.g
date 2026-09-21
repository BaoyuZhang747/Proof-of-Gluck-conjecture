# Exact fixed-point bounds for seventy-seven Holt--Yang candidate rows.  The
# bounds prove the existence of a regular orbit in thirty-six rows.  The
# remaining forty-one rows are settled by the separate calculations for the
# twenty-three small rows, the seventeen medium rows and row 2.
#
# The estimates are those in the proof of Theorem 3.1 of
#
#   Y. Yang, A. Vasil'ev and E. Vdovin,
#   Regular orbits of finite primitive solvable groups, III,
#   Journal of Algebra 590 (2022), 139--154,
#
# referred to below as YVV.  The estimates for fixed spaces come from
# Lemmas 2.4 and 2.5, the numbers of lifts from Lemmas 2.6 and 2.7, and the
# bounds for solvable completely reducible symplectic subgroups from
# Lemmas 2.8 and 2.9.
#
# The letters U, F and A have the meanings fixed in YVV Theorem 2.2.
# Write q=p^a and d=eab, as in YVV.  If the prime-order subgroups in the
# i-th part of the partition used in the proof of Theorem 3.1 number at
# most c_i and fix at most q^(beta_i*b) vectors, put
#
#             I = Sum_i c_i (q^(beta_i*b)-1),
#             R = q^(e*b)-1.
#
# The nonzero vectors fixed by a prime-order subgroup number at most I.
# Thus I<R leaves a nonzero vector fixed by no subgroup of prime order.
# Its stabiliser is trivial, since every nontrivial finite group contains
# a subgroup of prime order.  Consequently I<R proves a regular orbit for
# every group having the parameters of the row.
#
# The row numbers in this file are those of Holt--Yang, not YVV.  The two
# tables have the same numbering through row 103.  For the later rows used
# here the Holt--Yang to YVV correspondence is
#
#   114:113, 119:109, 120:111, 121:122, 122:126,
#   123:110, 124:105, 125:106, 126:121, 127:104.

DistinctPrimeDivisors := function(n)
    return Set(FactorsInt(n));
end;

# Lemma 2.6 writes U_s=gcd(|U|,s).  The cyclic group U has order dividing
# q-1, and hence U_s<=gcd(q-1,s).  The following linear terms retain this
# bound.  Whenever elements of order s are counted as subgroups of order s,
# their number is divided by s-1.

LinearBoundForE2 := function(q, b)
    # The first two parts contribute 6+12.  The order-3 part contributes
    # 2*2^2*U_3/(3-1)=4*U_3.  All three fixed-space exponents are b.
    return (18 + 4 * Gcd(q - 1, 3)) * (q ^ b - 1);
end;

LinearBoundForE3 := function(q, b)
    local additionalBadSubgroups;

    # The involutions outside F contribute 3^2*U_2 at exponent 2b.
    # A direct count in the extraspecial group of order 27 gives 12 good
    # scalar triples.  Their fixed-space exponents are 2b, b and zero.  If
    # 9 divides |U|, the same count allows at most 72 further bad subgroups,
    # each with fixed-space exponent b.  Since |U| divides q-1, including
    # this extra term whenever 9 divides q-1 gives a bound valid for every
    # possible U.  The subgroups in F\U contribute a further 13 at exponent b.
    additionalBadSubgroups := 0;
    if (q - 1) mod 9 = 0 then
        additionalBadSubgroups := 72;
    fi;

    return (9 * Gcd(q - 1, 2) + 12) * (q ^ (2 * b) - 1)
         + (25 + additionalBadSubgroups) * (q ^ b - 1);
end;

LinearBoundForE4 := function(q, b)
    local coefficientAtTwoB;

    # The paired good involutions contribute 60 at exponents 3b and b.
    # At exponent 2b there are 30 subgroups from F\U, at most 21*2^4*2
    # bad involutions, and the order-3 and order-5 contributions
    #
    #       8*2^4*U_3/(3-1),   4*2^4*U_5/(5-1).
    coefficientAtTwoB := 702
                       + 64 * Gcd(q - 1, 3)
                       + 16 * Gcd(q - 1, 5);

    return 60 * (q ^ (3 * b) - 1)
         + coefficientAtTwoB * (q ^ (2 * b) - 1)
         + 60 * (q ^ b - 1);
end;

LinearBoundForE8 := function(q, b)
    local otherOddPrimes, coefficientAtFourB;

    # Lemma 2.9(3) gives at most 242 elements of order 3 and at most six
    # prime-order elements whose orders are neither 2 nor 3.  Since the
    # latter orders divide |Sp(6,2)|, they are 5 and 7.  Their combined
    # contribution is bounded using the larger of U_5/4 and U_7/6.
    otherOddPrimes := Maximum([
        Gcd(q - 1, 5) / 4,
        Gcd(q - 1, 7) / 6]);

    # The paired good involutions contribute 360 at exponents 6b and 2b.
    # The terms at exponent 4b come respectively from F\U, bad involutions,
    # elements of order 3, and elements of order 5 or 7.
    coefficientAtFourB := 126
                        + 135 * 2 ^ 6 * Gcd(q - 1, 2)
                        + 242 * 2 ^ 6 * Gcd(q - 1, 3) / 2
                        + 6 * 2 ^ 6 * otherOddPrimes;

    return 360 * (q ^ (6 * b) - 1)
         + coefficientAtFourB * (q ^ (4 * b) - 1)
         + 360 * (q ^ (2 * b) - 1);
end;

LinearBoundForE9 := function(q, b)
    # In order, these are the five parts A_1,...,A_5 in the e=9 case of
    # the proof of YVV Theorem 3.1.  The factors 1/(s-1) convert bounds for
    # elements of order s into bounds for their subgroups.
    return 121 * (q ^ (3 * b) - 1)
         + (95 * 3 ^ 4 * Gcd(q - 1, 2)) * (q ^ (6 * b) - 1)
         + (16 * 3 ^ 5 / 6) * (q ^ (6 * b) - 1)
         + (95 * 3 ^ 5 / 2) * (q ^ (5 * b) - 1)
         + (64 * 3 ^ 4 * Gcd(q - 1, 5) / 4)
           * (q ^ (4 * b) - 1);
end;

LinearBoundForRow2 := function()
    local q, oddPrimeFactor;

    # Holt--Yang row 2 has e=16, q=5 and b=1.  The odd prime divisors of
    # |Sp(8,2)| are 3,5,7,17.  Lemmas 2.6 and 2.9(4), followed by division
    # by s-1, give the factor below for the fifth part of the YVV partition.
    q := 5;
    oddPrimeFactor := Maximum(List([3, 5, 7, 17],
        s -> Gcd(q - 1, s) / (s - 1)));
    Assert(0, oddPrimeFactor = 1 / 2);

    return   510 * (q ^ 8 - 1)
           + (90 * 2 ^ 2 * 2) * (q ^ 12 - 1)
           + (513 * 2 ^ 4 * 2) * (q ^ 10 - 1)
           + (939 * 2 ^ 8 * 2) * (q ^ 8 - 1)
           + (1883 * 2 ^ 8 * oddPrimeFactor) * (q ^ 8 - 1);
end;

# For a subgroup of prime order s outside A, Lemma 2.7 gives at most
#
#                    (q-1)/(t-1),  where t=p^(a/s),
#
# possible lifts through U.  Its fixed space has at most t^(eb) vectors.
# The remaining coefficient is |A/F|*|F/U|.  The bounds used by YVV are
#
#   e=2:  6*2^2,          e=3:  24*3^2,
#   e=4:  6^2*2*2^4,     e=8:  6^4*2^6,
#   e=9:  24^2*2*3^4.
#
# The quotient G/A is cyclic and its order divides a.  Summing over all
# distinct prime divisors of a may include primes absent from G/A, which
# only enlarges the bound.  No division by s-1 is made here: for a fixed
# nonidentity coset of G/A, a subgroup of order s contributes one element
# to that coset.

FieldCoefficient := function(e)
    if e = 2 then
        return 6 * 2 ^ 2;
    elif e = 3 then
        return 24 * 3 ^ 2;
    elif e = 4 then
        return 6 ^ 2 * 2 * 2 ^ 4;
    elif e = 8 then
        return 6 ^ 4 * 2 ^ 6;
    elif e = 9 then
        return 24 ^ 2 * 2 * 3 ^ 4;
    fi;
    Error("unexpected value of e in the field-automorphism estimate");
end;

FieldAutomorphismBound := function(e, p, a, b)
    local q, coefficient, total, s, t;

    if a = 1 then
        return 0;
    fi;

    q := p ^ a;
    coefficient := FieldCoefficient(e);
    total := 0;
    for s in DistinctPrimeDivisors(a) do
        t := p ^ (a / s);
        total := total
               + coefficient * (q - 1) / (t - 1)
                 * (t ^ (e * b) - 1);
    od;
    return total;
end;

RegularOrbitBound := function(r)
    local q, linear;

    q := r.p ^ r.a;
    if r.e = 2 then
        linear := LinearBoundForE2(q, r.b);
    elif r.e = 3 then
        linear := LinearBoundForE3(q, r.b);
    elif r.e = 4 then
        linear := LinearBoundForE4(q, r.b);
    elif r.e = 8 then
        linear := LinearBoundForE8(q, r.b);
    elif r.e = 9 then
        linear := LinearBoundForE9(q, r.b);
    elif r.e = 16 then
        Assert(0, r.row = 2 and r.p = 5 and r.a = 1 and r.b = 1);
        return LinearBoundForRow2();
    else
        Error("unexpected value of e");
    fi;

    return linear + FieldAutomorphismBound(r.e, r.p, r.a, r.b);
end;

ParameterRow := function(row, e, p, a, b)
    return rec(row := row, e := e, p := p, a := a, b := b);
end;

rows := [
    ParameterRow(  2,16, 5,1,1),
    ParameterRow(  4, 9, 7,1,1), ParameterRow(  5, 9,13,1,1),
    ParameterRow(  6, 9, 2,4,1), ParameterRow(  7, 9,19,1,1),
    ParameterRow(  8, 9, 5,2,1),
    ParameterRow( 11, 8, 7,1,1), ParameterRow( 12, 8, 3,2,1),
    ParameterRow( 13, 8,11,1,1), ParameterRow( 14, 8,13,1,1),
    ParameterRow( 15, 8,17,1,1), ParameterRow( 16, 8,19,1,1),
    ParameterRow( 17, 8, 5,2,1), ParameterRow( 18, 8, 3,3,1),

    ParameterRow( 26, 4,19,1,1), ParameterRow( 27, 4,23,1,1),
    ParameterRow( 29, 4, 3,3,1), ParameterRow( 30, 4,29,1,1),
    ParameterRow( 31, 4,31,1,1), ParameterRow( 32, 4,37,1,1),
    ParameterRow( 33, 4,41,1,1), ParameterRow( 34, 4,43,1,1),
    ParameterRow( 35, 4,47,1,1), ParameterRow( 36, 4, 7,2,1),
    ParameterRow( 37, 4,53,1,1), ParameterRow( 38, 4,59,1,1),
    ParameterRow( 39, 4,61,1,1), ParameterRow( 40, 4,67,1,1),
    ParameterRow( 41, 4,71,1,1), ParameterRow( 42, 4,73,1,1),
    ParameterRow( 43, 4, 3,4,1), ParameterRow( 44, 4,11,2,1),
    ParameterRow( 45, 4, 5,3,1), ParameterRow( 46, 4,13,2,1),
    ParameterRow( 47, 4, 3,5,1),

    ParameterRow( 54, 3, 7,2,1), ParameterRow( 56, 3,11,2,1),
    ParameterRow( 57, 3,13,2,1), ParameterRow( 58, 3, 2,8,1),
    ParameterRow( 59, 3,17,2,1), ParameterRow( 60, 3, 7,3,1),
    ParameterRow( 61, 3,19,2,1),

    ParameterRow( 70, 2,23,1,1), ParameterRow( 73, 2,29,1,1),
    ParameterRow( 79, 2, 3,5,1), ParameterRow( 81, 2, 7,3,1),
    ParameterRow( 82, 2,19,2,1), ParameterRow( 83, 2,23,2,1),
    ParameterRow( 85, 2, 3,6,1), ParameterRow( 86, 2,29,2,1),
    ParameterRow( 87, 2,31,2,1), ParameterRow( 88, 2,11,3,1),
    ParameterRow( 89, 2,37,2,1), ParameterRow( 90, 2,41,2,1),
    ParameterRow( 91, 2,43,2,1), ParameterRow( 92, 2, 3,7,1),
    ParameterRow( 93, 2,13,3,1), ParameterRow( 94, 2,47,2,1),
    ParameterRow( 95, 2, 7,4,1), ParameterRow( 96, 2,53,2,1),
    ParameterRow( 97, 2, 5,5,1), ParameterRow( 98, 2,59,2,1),
    ParameterRow( 99, 2,61,2,1), ParameterRow(100, 2,67,2,1),
    ParameterRow(101, 2,17,3,1), ParameterRow(102, 2,71,2,1),
    ParameterRow(103, 2,73,2,1),

    ParameterRow(114, 3, 7,1,2), ParameterRow(119, 4, 7,1,2),
    ParameterRow(120, 4,11,1,2), ParameterRow(121, 4, 3,1,3),
    ParameterRow(122, 4, 3,1,4), ParameterRow(123, 4, 3,2,2),
    ParameterRow(124, 8, 3,1,2), ParameterRow(125, 8, 5,1,2),
    ParameterRow(126, 8, 3,1,3), ParameterRow(127, 9, 2,2,2)
];

allRowNumbers := [
      2,  4,  5,  6,  7,  8, 11, 12, 13, 14, 15, 16, 17, 18,
     26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
     41, 42, 43, 44, 45, 46, 47,
     54, 56, 57, 58, 59, 60, 61,
     70, 73, 79, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92,
     93, 94, 95, 96, 97, 98, 99,100,101,102,103,
    114,119,120,121,122,123,124,125,126,127
];

Assert(0, Length(rows) = 77);
Assert(0, List(rows, r -> r.row) = allRowNumbers);
Assert(0, Length(Set(allRowNumbers)) = 77);

values := List(rows, function(r)
    local q, I, R;

    q := r.p ^ r.a;
    I := RegularOrbitBound(r);
    R := q ^ (r.e * r.b) - 1;
    Assert(0, IsInt(2 * I));
    return rec(row := r.row, e := r.e, p := r.p, a := r.a,
               b := r.b, q := q, I := I, R := R, difference := R - I);
end);

# The e=3 lift count differs from the displayed calculation in YVV only when
# 9 can divide |U|.  The proof in the accompanying paper shows that the lower
# bounds in YVV Table 3.2 are unchanged.  The assertions below check the
# finite boundary values left by the monotonic estimates in that proof.
E3ThresholdMargin := function(p, a, b)
    local q, bound;
    q := p ^ a;
    bound := LinearBoundForE3(q, b)
             + FieldAutomorphismBound(3, p, a, b);
    return q ^ (3 * b) - 1 - bound;
end;

Assert(0, E3ThresholdMargin(31, 1, 1) = 240);
Assert(0, E3ThresholdMargin(37, 1, 1) = 6120);
Assert(0, E3ThresholdMargin(13, 1, 2) = 3965808);
Assert(0, E3ThresholdMargin( 7, 1, 3) = 36815616);
Assert(0, E3ThresholdMargin( 2, 2, 4) = 12741045);

E3IntermediatePrimePowers := [
    [23,2], [5,4], [29,2], [31,2], [2,10], [37,2], [41,2],
    [43,2], [13,3], [47,2], [7,4], [53,2], [59,2], [61,2]
];
Assert(0, List(E3IntermediatePrimePowers,
               entry -> entry[1] ^ entry[2]) =
    [529,625,841,961,1024,1369,1681,1849,2197,2209,2401,
     2809,3481,3721]);
Assert(0, ForAll(E3IntermediatePrimePowers,
    entry -> E3ThresholdMargin(entry[1], entry[2], 1) > 0));
Assert(0, E3ThresholdMargin(23, 2, 1) = 76558944);

provedRows := List(Filtered(values, x -> x.difference > 0), x -> x.row);
undecidedRows := List(Filtered(values, x -> x.difference <= 0), x -> x.row);

expectedProvedRows := Concatenation(
    [18, 42, 45, 46, 47, 58, 59, 60, 61, 70, 73, 79, 81],
    [86 .. 103],
    [114, 120, 122, 125, 126]);
expectedUndecidedRows := Difference(allRowNumbers, expectedProvedRows);

Assert(0, provedRows = expectedProvedRows);
Assert(0, undecidedRows = expectedUndecidedRows);
Assert(0, Length(provedRows) = 36);
Assert(0, Length(undecidedRows) = 41);
Assert(0, List(Filtered(values, x -> not IsInt(x.I)), x -> x.row) = [6, 127]);

# One exact value for each value of e checks all six formulae independently
# of the comparison lists above.  Row 59 also checks the additional e=3
# term used when 9 divides q-1.
Assert(0, First(values, x -> x.row =   2).I = 618242229312);
Assert(0, 2 * First(values, x -> x.row = 6).I = 549612164115);
Assert(0, First(values, x -> x.row =  18).I = 159961836320);
Assert(0, First(values, x -> x.row =  45).I = 151697136);
Assert(0, First(values, x -> x.row =  58).I = 16419450);
Assert(0, First(values, x -> x.row =  59).I = 21631392);
Assert(0, First(values, x -> x.row =  60).I = 7773318);
Assert(0, First(values, x -> x.row =  61).I = 33571080);
Assert(0, First(values, x -> x.row =  59).difference = 2506176);
Assert(0, First(values, x -> x.row =  60).difference = 32580288);
Assert(0, First(values, x -> x.row =  61).difference = 13474800);
Assert(0, First(values, x -> x.row =  87).I = 766080);

for x in values do
    Print("Holt--Yang row ", x.row,
          ": e=", x.e, ", q=", x.q, ", b=", x.b,
          ", I=", x.I, ", R=", x.R,
          ", R-I=", x.difference);
    if x.difference > 0 then
        Print("  (I<R)\n");
    else
        Print("  (the bound is not strict)\n");
    fi;
od;

Print("\nThe strict inequality I<R holds for these 36 Holt--Yang rows:\n",
      provedRows, "\n");
Print("Every group having the parameters of one of these rows has a regular ",
      "orbit.\n");
Print("\nThe same bound is not strict for these 41 Holt--Yang rows:\n",
      undecidedRows, "\n");
Print("No conclusion about regular orbits in these 41 rows follows from this ",
      "inequality alone.\n");

QUIT_GAP(0);
