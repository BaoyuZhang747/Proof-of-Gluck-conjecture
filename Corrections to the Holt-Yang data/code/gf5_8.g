# Verification on GF(5)^8.

Read("gf5_8_constructions.g");
Line10gps := fail;;
Line28gps := fail;;

# Tables 2.1 and 2.2 give these four residual parameter rows on GF(5)^8.
ParameterRows58 := [
    ["10",  8, 1, 1, "two extraspecial-subgroup quotients"],
    ["28",  4, 2, 1, "semilinear normaliser quotients"],
    ["84",  2, 4, 1, "semilinear normaliser quotients"],
    ["118", 4, 1, 2, "repeated extraspecial-subgroup quotients"]
];;
RequireEqual("the list of parameter rows on GF(5)^8", ParameterRows58,
  [["10",8,1,1,"two extraspecial-subgroup quotients"],
   ["28",4,2,1,"semilinear normaliser quotients"],
   ["84",2,4,1,"semilinear normaliser quotients"],
   ["118",4,1,2,"repeated extraspecial-subgroup quotients"]]);

extraspecialNormalisers := Row10ExtraspecialNormalisers();;
plus := First(extraspecialNormalisers, entry -> entry.id = [128,2326]);;
minus := First(extraspecialNormalisers, entry -> entry.id = [128,2327]);;
RequireEqual("E+ orbit length", plus.orbitLength, 36);
RequireEqual("E- orbit length", minus.orbitLength, 28);
RequireEqual("order of N(E+)", Size(plus.M), 10321920);
RequireEqual("order of N(E-)", Size(minus.M), 13271040);
RequireEqual("order of N(E+)/E+", Size(plus.M)/128, 80640);
RequireEqual("order of N(E-)/E-", Size(minus.M)/128, 103680);

plusOrthogonalOrder := 2 * 2^6 * (2^3-1)
                       * Product([1 .. 2], i -> 2^(2*i)-1);;
minusOrthogonalOrder := 2 * 2^6 * (2^3+1)
                        * Product([1 .. 2], i -> 2^(2*i)-1);;
RequireEqual("order formula for O+(6,2)", plusOrthogonalOrder, 40320);
RequireEqual("order formula for O-(6,2)", minusOrthogonalOrder, 51840);
RequireEqual("full E+ normaliser quotient bound",
           Size(plus.M)/128, 2 * plusOrthogonalOrder);
RequireEqual("full E- normaliser quotient bound",
           Size(minus.M)/128, 2 * minusOrthogonalOrder);

Print("Row 10: enumerating subgroups above the symplectic-type subgroup S\n");
symplecticCoreResult := EnumerateQuotientGroups58(S, N, 1301);;
RequireEqual("order of the row-10 quotient",
           symplecticCoreResult.quotientOrder, 1451520);
symplecticCoreGroups := symplecticCoreResult.groups;;
RequireEqual("accepted groups containing S", Length(symplecticCoreGroups), 18);

Print("Row 10: enumerating the two extraspecial-subgroup normaliser quotients\n");
plusResult := EnumerateQuotientGroups58(plus.E, plus.M, 547);;
minusResult := EnumerateQuotientGroups58(minus.E, minus.M, 609);;
plusGroups := plusResult.groups;;
minusGroups := minusResult.groups;;
RequireEqual("order of the E+ quotient", plusResult.quotientOrder, 80640);
RequireEqual("order of the E- quotient", minusResult.quotientOrder, 103680);
RequireEqual("accepted E+ groups", Length(plusGroups), 0);
RequireEqual("accepted E- groups", Length(minusGroups), 22);

Print("Rows 28, 84 and 118: enumerating the two extraspecial-subgroup orbits\n");
row28Groups := EnumerateSmallerRow(28);;
row84Groups := EnumerateSmallerRow(84);;
row118Groups := EnumerateSmallerRow(118);;
RequireEqual("accepted row-28 groups", Length(row28Groups), 3);
RequireEqual("accepted row-84 groups", Length(row84Groups), 0);
RequireEqual("accepted row-118 groups", Length(row118Groups), 6);

invMinus := List(minusGroups,
                 CharacteristicPolynomialConjugacyInvariant);;
RequireEqual("pairwise distinct E- classes", Length(Set(invMinus)), 22);
for G in symplecticCoreGroups do
    RequireEqual("a group containing S occurs in the E- list",
               ExactMatchIndex(G, minusGroups, invMinus) > 0, true);
od;

ReadRequired("holt_yang_data/Line10gps.g");
ReadRequired("holt_yang_data/Line28gps.g");
RequireEqual("number of Holt--Yang row-10 groups", Length(Line10gps), 22);
RequireEqual("number of Holt--Yang row-28 groups", Length(Line28gps), 3);
line10Cover := HoltYangLine10InMinusNormaliser(Line10gps, minus.E, minus.M);;
RequireEqual("Holt--Yang row-10 groups in N(E-)",
           line10Cover.covered, 22);

line10Inv := List(Line10gps,
                  CharacteristicPolynomialConjugacyInvariant);;
RequireEqual("distinct Holt--Yang row-10 invariants",
           Length(Set(line10Inv)), 22);
RequireEqual("row-10 invariant-multiset comparison",
           Collected(invMinus), Collected(line10Inv));
line10Matches := List(Line10gps,
    G -> ExactMatchIndex(G, minusGroups, invMinus));;
RequireEqual("exact Line10 to E- bijection",
           Set(line10Matches), [1 .. 22]);

line28Inv := List(Line28gps,
                  CharacteristicPolynomialConjugacyInvariant);;
matches := List(row28Groups,
                G -> ExactMatchIndex(G, Line28gps, line28Inv));;
RequireEqual("row 28 maps bijectively to Line28", Set(matches), [1,2,3]);
RequireEqual("distinct Holt--Yang row-28 invariants",
           Length(Set(line28Inv)), 3);
RequireEqual("Line28 and Line10 are disjoint GL(8,5)-classes",
  ForAll([1 .. Length(Line28gps)], i ->
    ForAll([1 .. Length(Line10gps)], j ->
      line28Inv[i] <> line10Inv[j]
      or not AreConjugateInGL(Line28gps[i], Line10gps[j], 5))), true);
distinctSpaceClasses := Length(Line10gps) + Length(Line28gps);;
RequireEqual("number of distinct classes on GF(5)^8",
           distinctSpaceClasses, 25);

n28 := 0;;
n10 := 0;;
unmatched := 0;;
for G in row118Groups do
    j := ExactMatchIndex(G, Line28gps, line28Inv);
    if j > 0 then
        n28 := n28 + 1;
    else
        j := ExactMatchIndex(G, Line10gps, line10Inv);
        if j > 0 then n10 := n10 + 1;
        else unmatched := unmatched + 1;
        fi;
    fi;
od;
RequireEqual("row-118 groups belonging to Line28", n28, 3);
RequireEqual("row-118 groups belonging to Line10", n10, 3);
RequireEqual("unmatched row-118 groups", unmatched, 0);

Print("Rows 10, 28, 84 and 118 yield 25 distinct GL(8,5)-classes.  The ",
      "22 Line10 and 3 Line28 records account for all of them; rows 84 and ",
      "118 introduce no further class.\n");
QUIT_GAP(0);
