# Exact normaliser-quotient verification on GF(2)^18.
#
# The extraspecial group E=3^{1+4} is irreducible in dimension 9 over GF(4).
# Its centre contains all nonzero scalars from GF(4), so restriction to GF(2)
# remains irreducible in
# dimension 18; this is also checked directly below.  Every qualifying group contains a
# conjugate of E normally, so the exhaustive search is the solvable part of the
# conjugacy classes of subgroups of N/E, where N is the normaliser of E in
# GL(18,2).  Explicit generators for N avoid the full ambient normaliser
# calculation.  The program also aligns the
# characteristic O_3 subgroup of every Holt--Yang group with E and checks its
# conjugate lies in N before using the exact 40-to-40 counting argument.
# Rows 55 and 116 prescribe conjugate normal subgroups of order 27.  Their
# common full normaliser is treated after the row-3 calculation, and every lift
# satisfying the five conditions is compared exactly with the row-3 list.

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

RequireAndRead := function(path)
    if not IsReadableFile(path) then
        Error("The required input file is missing or unreadable: ", path);
    fi;
    Read(path);
end;;

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

RequireAndRead("matrix_group_tests.g");

HoltYangDataDir := "holt_yang_data/";;

RequireAndRead(Concatenation(HoltYangDataDir, "Line3gps.g"));
if not IsBoundGlobal("Line3gps") then
    Error("The file Line3gps.g did not define the list Line3gps.");
fi;
holtYangGroups := Line3gps;;
Print("Holt--Yang groups on GF(2)^18 read: ",
      Length(holtYangGroups), "\n");

# These are the three candidate-table rows on GF(2)^18.
ParameterRows := [
    rec(row := "3", p := 2, e := 9, a := 2, b := 1,
        enumeration := "subgroups of N/E, with N the normaliser of E in GL(18,2)"),
    rec(row := "55", p := 2, e := 3, a := 6, b := 1,
        enumeration := "subgroups covered by the common order-27 normaliser"),
    rec(row := "116", p := 2, e := 3, a := 2, b := 3,
        enumeration := "subgroups covered by the common order-27 normaliser")
];;
RequireEqual("the parameter-row census on GF(2)^18",
             List(ParameterRows,
                  row -> [row.row, row.p, row.e, row.a, row.b, row.enumeration]),
             [["3", 2, 9, 2, 1,
               "subgroups of N/E, with N the normaliser of E in GL(18,2)"],
              ["55", 2, 3, 6, 1,
               "subgroups covered by the common order-27 normaliser"],
              ["116", 2, 3, 2, 3,
               "subgroups covered by the common order-27 normaliser"]]);

# 1. The prescribed normal subgroup for row 3.

# Each generator is given as a list of row supports: entry j of row i lists
# the columns in which that row has the value 1 over GF(2).  The four matrices
# below generate a group of order 243 with centre of order 3 -- the
# extraspecial group 3^{1+4} of exponent 3 -- realised as the 18-dimensional
# GF(2)-representation obtained from its faithful 9-dimensional representation
# over GF(4).

MatrixFromRowSupports := function(rows)
    local d, m, i, c;
    d := Length(rows);
    m := NullMat(d, d, GF(2));
    for i in [1 .. d] do
        for c in rows[i] do
            m[i][c] := Z(2)^0;
        od;
    od;
    return m;
end;;

coreSupports := [
  [ [7],[8],[9],[10],[11],[12],[13],[14],[15],[16],[17],[18],
    [1],[2],[3],[4],[5],[6] ],
  [ [1],[2],[3],[4],[5],[6],[8],[7,8],[10],[9,10],[12],[11,12],
    [13,14],[13],[15,16],[15],[17,18],[17] ],
  [ [3],[4],[5],[6],[1],[2],[9],[10],[11],[12],[7],[8],
    [15],[16],[17],[18],[13],[14] ],
  [ [1],[2],[4],[3,4],[5,6],[5],[7],[8],[10],[9,10],[11,12],[11],
    [13],[14],[16],[15,16],[17,18],[17] ] ];;

coreGens := List(coreSupports, MatrixFromRowSupports);;
Ecore := Group(coreGens);;
Print("Extraspecial subgroup E:  |E| = ", Size(Ecore),
      ",  |Z(E)| = ", Size(Centre(Ecore)),
      ",  exponent = ", Exponent(Ecore), "\n");
RequireEqual("order of E", Size(Ecore), 243);
RequireEqual("order of the centre of E", Size(Centre(Ecore)), 3);
RequireEqual("exponent of E", Exponent(Ecore), 3);

# E already acts irreducibly on V = GF(2)^18, so irreducibility is automatic
# for every group containing E.
coreModule := GModuleByMats(coreGens, GF(2));;
RequireEqual("E acts irreducibly on GF(2)^18",
          MTX.IsIrreducible(coreModule), true);
coreEndomorphisms := MTX.BasisModuleEndomorphisms(coreModule);;
RequireEqual("dimension of the E-endomorphism field over GF(2)",
          Length(coreEndomorphisms), 2);

# 2. The normaliser N of E in GL(18,2) and the quotient Q=N/E.

# The irreducible endomorphism algebra just computed is GF(4), and its three
# nonzero scalars form Z(E).  The extraspecial-normaliser theorem therefore
# bounds N/E by Sp(4,3):2.  Its order is
#
#   2 |Sp(4,3)| = 2 * 3^4 * (3^2-1) * (3^4-1) = 103680.
#
# N is generated by E and the displayed matrices.  Normality and attainment
# of this upper bound prove that the displayed N is the full normaliser.

normaliserExtraSupports := [
  [ [2],[1,2],[3],[4],[5],[6],[8],[7,8],[9],[10],[11],[12],
    [14],[13,14],[15],[16],[17],[18] ],
  [ [1],[2],[7],[8],[13],[14],[3],[4],[9],[10],[15],[16],
    [5],[6],[11],[12],[17],[18] ],
  [ [2],[1,2],[7,8],[7],[13],[14],[3,4],[3],[10],[9,10],[15],[16],
    [5],[6],[11],[12],[17],[18] ],
  [ [5],[6],[9],[10],[13],[14],[3],[4],[7],[8],[17],[18],
    [1],[2],[11],[12],[15],[16] ],
  [ [5],[6],[7],[8],[15],[16],[1],[2],[9],[10],[17],[18],
    [3],[4],[11],[12],[13],[14] ],
  [ [1,4,5,6],[2,3,4,5],[13,15,16,18],[14,15,17,18],[7,9,11],[8,10,12],
    [1,3,5],[2,4,6],[13,16,17,18],[14,15,16,17],[7,9,10,12],[8,9,11,12],
    [1,3,4,6],[2,3,5,6],[13,15,17],[14,16,18],[7,10,11,12],[8,9,10,11] ],
  [ [1],[1,2],[3],[3,4],[5],[5,6],[7],[7,8],[9],[9,10],[11],[11,12],
    [13],[13,14],[15],[15,16],[17],[17,18] ] ];;

normaliserGens := Concatenation(coreGens,
                    List(normaliserExtraSupports, MatrixFromRowSupports));;
N := Group(normaliserGens);;
Print("The normaliser of E in GL(18,2) has order ", Size(N), ".\n");
RequireEqual("E is contained and normal in N", IsNormal(N, Ecore), true);
RequireEqual("order of the normaliser of E in GL(18,2)", Size(N), 25194240);
normaliserQuotientBound := 2 * 3^4 * (3^2-1) * (3^4-1);;
RequireEqual("order formula for Sp(4,3):2", normaliserQuotientBound, 103680);
RequireEqual("the constructed normaliser attains the upper bound",
          Size(N) / Size(Ecore), normaliserQuotientBound);

# The Holt--Yang matrices need not use this copy of E.  For each group we
# recover its characteristic O_3 subgroup, construct a change of basis taking
# that subgroup to E, and verify that the conjugated Holt--Yang group lies in N.
# This is the inclusion needed for the subsequent counting argument.
PrescribedSubgroupConjugator := function(source, target)
    local iso, gens, imgs, x;
    iso := IsomorphismGroups(source, target);
    if iso = fail then return fail; fi;
    gens := GeneratorsOfGroup(source);
    imgs := List(gens, g -> Image(iso, g));
    x := MTX.IsomorphismModules(GModuleByMats(gens, GF(2)),
                               GModuleByMats(imgs, GF(2)));
    if x = fail or RankMat(x) <> 18 then return fail; fi;
    if not ForAll([1 .. Length(gens)],
                  i -> x^-1 * gens[i] * x = imgs[i]) then return fail; fi;
    if source ^ x <> target then return fail; fi;
    return x;
end;;

line3AlignmentMatrices := [];;
for H in holtYangGroups do
    O3 := PCore(H, 3);
    RequireEqual("order of O_3(H) for a Holt--Yang group", Size(O3), 243);
    RequireEqual("centre of O_3(H) for a Holt--Yang group",
              Size(Centre(O3)), 3);
    RequireEqual("exponent of O_3(H) for a Holt--Yang group",
              Exponent(O3), 3);
    x := PrescribedSubgroupConjugator(O3, Ecore);
    RequireEqual("linear conjugator from O_3(H) to E",
              x <> fail, true);
    RequireEqual("conjugated Holt--Yang group lies in N",
              IsSubgroup(N, H ^ x), true);
    Add(line3AlignmentMatrices, x);
od;
Print("Holt--Yang groups conjugated into the normaliser of E in GL(18,2): ",
      Length(line3AlignmentMatrices), "/", Length(holtYangGroups), "\n");

RequireEqual("number of E-alignment matrices",
          Length(line3AlignmentMatrices), Length(holtYangGroups));
for i in [1 .. Length(holtYangGroups)] do
    x := line3AlignmentMatrices[i];
    O3 := PCore(holtYangGroups[i], 3);
    RequireEqual("E-alignment matrix has full rank", RankMat(x), 18);
    RequireEqual("computed matrix maps O_3(H) onto E",
              O3 ^ x, Ecore);
    RequireEqual("computed matrix gives containment in the normaliser",
              IsSubgroup(N, holtYangGroups[i] ^ x), true);
od;
alignedHoltYangGroups := List([1 .. Length(holtYangGroups)],
  i -> holtYangGroups[i] ^ line3AlignmentMatrices[i]);;

quo := NaturalHomomorphismByNormalSubgroup(N, Ecore);;
Q := Image(quo);;
RequireEqual("order of the quotient Q = N/E", Size(Q), 103680);
RequireEqual("the quotient N/E has trivial 3-core",
          Size(PCore(Q, 3)), 1);
RequireEqual("Q = N/E is non-solvable (it is Sp(4,3):2)",
          IsSolvableGroup(Q), false);
Print("The quotient N/E has order ", Size(Q), " and is not solvable.\n");

# 3. Complete enumeration of the conjugacy classes of subgroups of Q.

# Only the solvable subgroups can lift to a solvable G, so we retain the
# solvable classes for the filtering step.

subgroupClasses := ConjugacyClassesSubgroups(Q);;
Print("Subgroup classes of Q: ", Length(subgroupClasses), "\n");
RequireEqual("number of subgroup classes of Q", Length(subgroupClasses), 492);

solvableClasses := Filtered(subgroupClasses,
                     cl -> IsSolvableGroup(Representative(cl)));;
Print("Solvable subgroup classes of Q: ", Length(solvableClasses), "\n");
RequireEqual("number of solvable subgroup classes of Q",
          Length(solvableClasses), 473);

# 4. Lifting each solvable class to GL(18,2) and applying the five criteria.

# The less expensive criteria are applied first.  If |G| >= |V|, then no
# orbit on V can be regular; otherwise the program checks the nonzero vectors.
# It then tests irreducibility -- automatic here -- followed by
# quasiprimitivity and nonmetacyclicity.  All of these are the shared routines
# in matrix_group_tests.g.

accepted := [];;
for cl in solvableClasses do
    G := PreImage(quo, Representative(cl));
    if HasNoRegularOrbit(G, 2, 18)
       and MTX.IsIrreducible(GModuleByMats(GeneratorsOfGroup(G), GF(2)))
       and IsQuasiprimitiveLinearGroup(G, 2, 18)
       and not IsMetacyclicSolvableGroup(G)
    then
        Add(accepted, G);
    fi;
od;
Print("Groups meeting all five criteria: ", Length(accepted), "\n");
RequireEqual("number of groups satisfying the five criteria",
          Length(accepted), 40);

# 5. Exact comparison with the Holt--Yang data.

# Both an aligned Holt--Yang group and an accepted group contain E.  Quotient
# conjugacy supplies possible matches in Q=N/E.  For each possible match we
# lift a quotient conjugator to N and then require equality of the full
# 18-dimensional matrix groups; that direct equality proves the bijection.

RequireEqual("number of Holt--Yang groups", Length(holtYangGroups), 40);
RequireEqual("Holt--Yang groups contained in the normaliser of E in GL(18,2) after alignment",
          Length(line3AlignmentMatrices), 40);
RequireEqual("Holt--Yang groups satisfying all five target conditions",
          Number(holtYangGroups,
                 H -> SatisfiesHoltYangCriteria(H, 2, 18)), 40);

acceptedImages := List(accepted, G -> Image(quo, G));;
matchIndices := [];;
matchingConjugators := [];;
holtYangMatched := [];;
for i in [1 .. Length(holtYangGroups)] do
    holtYangImage := Image(quo, alignedHoltYangGroups[i]);
    candidateIndices := [];
    candidateMatrices := [];
    for j in [1 .. Length(accepted)] do
        if Size(holtYangImage) = Size(acceptedImages[j]) then
            quotientConjugator := RepresentativeAction(
                Q, holtYangImage, acceptedImages[j]);
            if quotientConjugator <> fail then
                liftedConjugator := PreImagesRepresentative(
                    quo, quotientConjugator);
                fullConjugator :=
                  line3AlignmentMatrices[i]
                  * liftedConjugator;
                if holtYangGroups[i] ^ fullConjugator = accepted[j] then
                    Add(candidateIndices, j);
                    Add(candidateMatrices, fullConjugator);
                fi;
            fi;
        fi;
    od;
    RequireEqual("unique exact accepted match for a Holt--Yang group",
              Length(candidateIndices), 1);
    Add(matchIndices, candidateIndices[1]);
    Add(matchingConjugators, candidateMatrices[1]);
    Add(holtYangMatched, true);
od;
RequireEqual("the exact matches form a bijection",
          Set(matchIndices), [1 .. Length(accepted)]);

RequireEqual("number of exact-match matrices", Length(matchingConjugators), 40);
for i in [1 .. Length(holtYangGroups)] do
    x := matchingConjugators[i];
    j := matchIndices[i];
    RequireEqual("exact-match matrix has full rank", RankMat(x), 18);
    RequireEqual("computed matrix gives full group equality",
              holtYangGroups[i] ^ x, accepted[j]);
od;

# The conjugacy invariant is not used to prove the match.  It supplies a
# compact, independently recomputed comparison after the exact matrix equalities.
acceptedInvariants := List(accepted,
                           CharacteristicPolynomialConjugacyInvariant);;
holtYangInvariants := List(holtYangGroups,
                           CharacteristicPolynomialConjugacyInvariant);;
RequireEqual("the forty accepted groups have pairwise distinct invariants",
          Length(Set(acceptedInvariants)), 40);

additionalClasses := Difference([1 .. Length(accepted)], Set(matchIndices));;
unrecoveredHoltYangClasses := Positions(holtYangMatched, false);;
RequireEqual("enumerated classes absent from the Holt--Yang data",
             Length(additionalClasses), 0);
RequireEqual("Holt--Yang classes not recovered by the enumeration",
             Length(unrecoveredHoltYangClasses), 0);

RequireEqual("conjugacy-invariant multiset comparison",
          Collected(acceptedInvariants) = Collected(holtYangInvariants), true);

# The multiset of group orders also matches, class for class.
RequireEqual("order multisets of enumerated and Holt--Yang groups agree",
          Collected(List(accepted, Size)) = Collected(List(holtYangGroups, Size)),
          true);

Print("The 492 subgroup classes of N/E contain 473 solvable classes.  Exactly ",
      "40 lifts satisfy the five conditions, and direct 18-dimensional ",
      "matrix equalities give a bijection with the 40 Line3 records.\n");

# 6. The prescribed normal subgroups for rows 55 and 116.

# An order-27 extraspecial group acts absolutely irreducibly in dimension 3
# over GF(4).  Rows 55 and 116 both restrict to three copies of this module
# over GF(2).  The following routines use the same field-reduction and tensor
# ordering as the small-space program.

FieldMultiplicationMatrix := function(K, F, basis, alpha)
    local a, out, i, j, coeffs;
    a := Length(basis);
    out := NullMat(a, a, F);
    for i in [1 .. a] do
        coeffs := Coefficients(basis, basis[i] * alpha);
        for j in [1 .. a] do
            out[i][j] := coeffs[j];
        od;
    od;
    return out;
end;;

RestrictionOfScalarsMatrix := function(K, F, mat)
    local basis, a, m, out, i, j, block, bi, bj;
    basis := Basis(K);
    a := Length(basis);
    m := Length(mat);
    out := NullMat(m * a, m * a, F);
    for i in [1 .. m] do
        for j in [1 .. m] do
            block := FieldMultiplicationMatrix(K, F, basis, mat[i][j]);
            for bi in [1 .. a] do
                for bj in [1 .. a] do
                    out[(i - 1) * a + bi][(j - 1) * a + bj] := block[bi][bj];
                od;
            od;
        od;
    od;
    return out;
end;;

TensorLocalMatrix := function(A, b, K)
    local e, out, i, j, r;
    e := Length(A);
    out := NullMat(e * b, e * b, K);
    for i in [1 .. e] do
        for j in [1 .. e] do
            for r in [1 .. b] do
                out[(i - 1) * b + r][(j - 1) * b + r] := A[i][j];
            od;
        od;
    od;
    return out;
end;;

TensorMultiplicityMatrix := function(B, e, K)
    local b, out, i, r, c;
    b := Length(B);
    out := NullMat(e * b, e * b, K);
    for i in [1 .. e] do
        for r in [1 .. b] do
            for c in [1 .. b] do
                out[(i - 1) * b + r][(i - 1) * b + c] := B[r][c];
            od;
        od;
    od;
    return out;
end;;

FieldFrobeniusMatrix := function(K, F)
    local basis, a, out, i, j, coeffs;
    basis := Basis(K);
    a := Length(basis);
    out := NullMat(a, a, F);
    for i in [1 .. a] do
        coeffs := Coefficients(basis, basis[i] ^ Size(F));
        for j in [1 .. a] do
            out[i][j] := coeffs[j];
        od;
    od;
    return out;
end;;

RepeatDiagonalBlock := function(block, copies, F)
    local a, out, k, i, j;
    a := Length(block);
    out := NullMat(a * copies, a * copies, F);
    for k in [1 .. copies] do
        for i in [1 .. a] do
            for j in [1 .. a] do
                out[(k - 1) * a + i][(k - 1) * a + j] := block[i][j];
            od;
        od;
    od;
    return out;
end;;

Extraspecial27Generators := function(K)
    local z, o, omega, X, D;
    z := Zero(K);
    o := One(K);
    omega := Z(Size(K)) ^ ((Size(K) - 1) / 3);
    X := [[z, o, z], [z, z, o], [o, z, z]];
    D := [[o, z, z], [z, omega, z], [z, z, omega^2]];
    return [X, D];
end;;

ParameterPrescribedSubgroup := function(row)
    local F, K, localGenerators, generators;
    F := GF(row.p);
    K := GF(row.p ^ row.a);
    localGenerators := Extraspecial27Generators(K);
    generators := List(localGenerators,
        A -> TensorLocalMatrix(A, row.b, K));
    return Group(List(generators, A -> RestrictionOfScalarsMatrix(K, F, A)));
end;;

baseField := GF(2);;
minimalField := GF(4);;
localNormalSubgroupK := Group(Extraspecial27Generators(minimalField));;
localNormaliserK := Normalizer(GL(3, minimalField), localNormalSubgroupK);;

RequireEqual("order of the local prescribed normal subgroup",
    Size(localNormalSubgroupK), 27);
RequireEqual("centre of the local prescribed normal subgroup",
    Size(Centre(localNormalSubgroupK)), 3);
RequireEqual("exponent of the local prescribed normal subgroup",
    Exponent(localNormalSubgroupK), 3);
RequireEqual("absolute irreducibility of the local prescribed normal subgroup",
    MTX.IsAbsolutelyIrreducible(
        GModuleByMats(GeneratorsOfGroup(localNormalSubgroupK), minimalField)), true);
RequireEqual("local prescribed normal subgroup is normal in its normaliser",
    IsNormal(localNormaliserK, localNormalSubgroupK), true);
RequireEqual("order of the local normaliser", Size(localNormaliserK), 648);
localNormaliserThreeCore := PCore(localNormaliserK, 3);;
localIntrinsicSubgroup := Group(Filtered(
    Elements(localNormaliserThreeCore),
    x -> x^3 = One(localNormaliserThreeCore)));;
RequireEqual("intrinsic subgroup of the local normaliser",
    localIntrinsicSubgroup, localNormalSubgroupK);

order27SubgroupOverMinimalField := Group(List(GeneratorsOfGroup(localNormalSubgroupK),
    A -> TensorLocalMatrix(A, 3, minimalField)));;
order27Subgroup := Group(List(GeneratorsOfGroup(order27SubgroupOverMinimalField),
    A -> RestrictionOfScalarsMatrix(minimalField, baseField, A)));;
order27LocalAction := Group(List(GeneratorsOfGroup(localNormaliserK),
    A -> RestrictionOfScalarsMatrix(minimalField, baseField,
                         TensorLocalMatrix(A, 3, minimalField))));;

multiplicityGroupOverMinimalField := Group(List(GeneratorsOfGroup(GL(3, minimalField)),
    B -> TensorMultiplicityMatrix(B, 3, minimalField)));;
multiplicityGroup := Group(List(GeneratorsOfGroup(multiplicityGroupOverMinimalField),
    B -> RestrictionOfScalarsMatrix(minimalField, baseField, B)));;

order27LinearNormaliser := ClosureGroup(order27LocalAction, multiplicityGroup);;
order27Frobenius := RepeatDiagonalBlock(
    FieldFrobeniusMatrix(minimalField, baseField), 9, baseField);;
order27Normaliser := Group(Concatenation(
    GeneratorsOfGroup(order27LinearNormaliser), [order27Frobenius]));;

RequireEqual("order of the prescribed normal subgroup",
    Size(order27Subgroup), 27);
RequireEqual("centre of the prescribed normal subgroup",
    Size(Centre(order27Subgroup)), 3);
RequireEqual("exponent of the prescribed normal subgroup",
    Exponent(order27Subgroup), 3);
RequireEqual("the prescribed normal subgroup is homogeneous",
    ActsHomogeneously(order27Subgroup, 2, 18), true);
RequireEqual("the repeated prescribed normal subgroup is reducible",
    MTX.IsIrreducible(GModuleByMats(
        GeneratorsOfGroup(order27Subgroup), baseField)), false);

order27Module := GModuleByMats(
    GeneratorsOfGroup(order27Subgroup), baseField);;
order27Endomorphisms := MTX.BasisModuleEndomorphisms(order27Module);;
RequireEqual("dimension of the endomorphism algebra",
    Length(order27Endomorphisms), 18);
RequireEqual("faithful local normaliser action",
    Size(order27LocalAction), Size(localNormaliserK));
RequireEqual("order of the multiplicity group",
    Size(multiplicityGroup), Size(GL(3, 4)));
RequireEqual("multiplicity group centralises the prescribed normal subgroup",
    ForAll(GeneratorsOfGroup(multiplicityGroup), g ->
        ForAll(GeneratorsOfGroup(order27Subgroup), e -> g * e = e * g)),
    true);
RequireEqual("local and multiplicity actions commute",
    ForAll(GeneratorsOfGroup(multiplicityGroup), g ->
        ForAll(GeneratorsOfGroup(order27LocalAction), h -> g * h = h * g)), true);
RequireEqual("intersection of the two linear tensor factors",
    Size(Intersection(order27LocalAction, multiplicityGroup)), 3);

multiplicityAlgebra := AlgebraWithOne(
    baseField, GeneratorsOfGroup(multiplicityGroup));;
RequireEqual("dimension of the explicit multiplicity algebra",
    Dimension(multiplicityAlgebra), 18);
RequireEqual("order of the linear normaliser",
    Size(order27LinearNormaliser), 39191040);
RequireEqual("Frobenius has order two", Order(order27Frobenius), 2);
RequireEqual("Frobenius normalises the prescribed normal subgroup",
    order27Subgroup ^ order27Frobenius, order27Subgroup);
RequireEqual("Frobenius normalises the linear normaliser",
    order27LinearNormaliser ^ order27Frobenius, order27LinearNormaliser);
RequireEqual("prescribed normal subgroup is normal in the constructed normaliser",
    IsNormal(order27Normaliser, order27Subgroup), true);
RequireEqual("local action is normal in the constructed normaliser",
    IsNormal(order27Normaliser, order27LocalAction), true);

order27PcGroup := Image(IsomorphismPcGroup(order27Subgroup));;
order27AutomorphismOrder := Size(AutomorphismGroup(order27PcGroup));;
RequireEqual("order of the automorphism group of the prescribed subgroup",
    order27AutomorphismOrder, 432);
order27NormaliserUpperBound := Size(multiplicityGroup)
                             * order27AutomorphismOrder;;
RequireEqual("order of the constructed full normaliser",
    Size(order27Normaliser), 78382080);
RequireEqual("attainment of the centraliser-automorphism upper bound",
    Size(order27Normaliser), order27NormaliserUpperBound);

# 7. Two solvable irreducible overgroups cover all cases.

# Quotienting by the solvable local action leaves PGammaL(3,4).  If a
# solvable irreducible group contains the prescribed normal subgroup, its
# image is solvable and its full preimage is irreducible.  The maximal such
# preimages therefore cover every group under consideration up to conjugacy.

multiplicityQuotientMap := NaturalHomomorphismByNormalSubgroup(
    order27Normaliser, order27LocalAction);;
multiplicityQuotient := Image(multiplicityQuotientMap);;
RequireEqual("order of the local-factor quotient",
    Size(multiplicityQuotient), 120960);
RequireEqual("the local-factor quotient is nonsolvable",
    IsSolvableGroup(multiplicityQuotient), false);

multiplicityQuotientClasses := ConjugacyClassesSubgroups(multiplicityQuotient);;
RequireEqual("subgroup classes of the local-factor quotient",
    Length(multiplicityQuotientClasses), 226);

solvableIrreducibleMultiplicityClasses := [];;
for class in multiplicityQuotientClasses do
    multiplicityQuotientSubgroup := Representative(class);
    if IsSolvableGroup(multiplicityQuotientSubgroup) then
        coveringOvergroup := PreImage(
            multiplicityQuotientMap, multiplicityQuotientSubgroup);
        if MTX.IsIrreducible(GModuleByMats(
            GeneratorsOfGroup(coveringOvergroup), baseField)) then
            Add(solvableIrreducibleMultiplicityClasses, class);
        fi;
    fi;
od;
RequireEqual("solvable irreducible quotient classes",
    Length(solvableIrreducibleMultiplicityClasses), 29);

maximalMultiplicityCoverClasses := Filtered(
    solvableIrreducibleMultiplicityClasses, class ->
        ForAll(solvableIrreducibleMultiplicityClasses, larger ->
            Size(Representative(larger)) <= Size(Representative(class))
            or ContainedConjugates(multiplicityQuotient,
                   Representative(larger), Representative(class), true)
               = fail));;
SortBy(maximalMultiplicityCoverClasses, class -> Size(Representative(class)));
RequireEqual("number of maximal solvable irreducible overgroups",
    Length(maximalMultiplicityCoverClasses), 2);
RequireEqual("orders of the maximal quotient groups",
    List(maximalMultiplicityCoverClasses, class -> Size(Representative(class))),
    [126, 432]);

for class in solvableIrreducibleMultiplicityClasses do
    RequireEqual("maximal-cover containment for a quotient class",
        ForAny(maximalMultiplicityCoverClasses, maximal ->
            ContainedConjugates(multiplicityQuotient, Representative(maximal),
                Representative(class), true) <> fail), true);
od;

ScanOrder27CoveringOvergroup := function(coveringOvergroup, prescribedSubgroup)
    local quotientMap, quotient, classes, qualifyingGroups,
          irreducibleCount, quasiprimitiveCount, nonmetacyclicCount, class, G;
    RequireEqual("a covering overgroup is solvable",
        IsSolvableGroup(coveringOvergroup), true);
    RequireEqual("the prescribed subgroup is normal in a covering overgroup",
        IsNormal(coveringOvergroup, prescribedSubgroup), true);
    quotientMap := NaturalHomomorphismByNormalSubgroup(
        coveringOvergroup, prescribedSubgroup);
    quotient := Image(quotientMap);
    classes := ConjugacyClassesSubgroups(quotient);
    qualifyingGroups := [];
    irreducibleCount := 0;
    quasiprimitiveCount := 0;
    nonmetacyclicCount := 0;
    for class in classes do
        G := PreImage(quotientMap, Representative(class));
        if MTX.IsIrreducible(
            GModuleByMats(GeneratorsOfGroup(G), GF(2))) then
            irreducibleCount := irreducibleCount + 1;
            if IsQuasiprimitiveLinearGroup(G, 2, 18) then
                quasiprimitiveCount := quasiprimitiveCount + 1;
                if not IsMetacyclicSolvableGroup(G) then
                    nonmetacyclicCount := nonmetacyclicCount + 1;
                    if HasNoRegularOrbit(G, 2, 18) then
                        Add(qualifyingGroups, G);
                    fi;
                fi;
            fi;
        fi;
    od;
    return rec(coveringOvergroupOrder := Size(coveringOvergroup),
               quotientOrder := Size(quotient),
               classCount := Length(classes),
               irreducibleCount := irreducibleCount,
               quasiprimitiveCount := quasiprimitiveCount,
               nonmetacyclicCount := nonmetacyclicCount,
               qualifyingGroups := qualifyingGroups);
end;;

coveringOvergroupResults := [];;
for class in maximalMultiplicityCoverClasses do
    coveringOvergroup := PreImage(
        multiplicityQuotientMap, Representative(class));
    Add(coveringOvergroupResults,
        ScanOrder27CoveringOvergroup(
            coveringOvergroup, order27Subgroup));
od;

RequireEqual("orders of the two covering overgroups",
    List(coveringOvergroupResults, r -> r.coveringOvergroupOrder), [81648, 279936]);
RequireEqual("orders of the covering-overgroup quotients by the prescribed subgroup",
    List(coveringOvergroupResults, r -> r.quotientOrder), [3024, 10368]);
RequireEqual("subgroup-class counts in the covering-overgroup quotients",
    List(coveringOvergroupResults, r -> r.classCount), [234, 745]);
RequireEqual("irreducible lift counts",
    List(coveringOvergroupResults, r -> r.irreducibleCount), [199, 339]);
RequireEqual("quasiprimitive lift counts",
    List(coveringOvergroupResults, r -> r.quasiprimitiveCount), [61, 68]);
RequireEqual("nonmetacyclic lift counts",
    List(coveringOvergroupResults, r -> r.nonmetacyclicCount), [61, 68]);
RequireEqual("numbers of lifts satisfying the five conditions",
    List(coveringOvergroupResults, r -> Length(r.qualifyingGroups)), [0, 9]);

order27QualifyingGroups := Concatenation(
    List(coveringOvergroupResults, r -> r.qualifyingGroups));;
RequireEqual("total number of lifts satisfying the five conditions",
    Length(order27QualifyingGroups), 9);
RequireEqual("orders of O_3 in these nine lifts",
    Set(List(order27QualifyingGroups, G -> Size(PCore(G, 3)))), [243]);

# The two parameter constructions are conjugate to the prescribed subgroup.

row55Record := First(ParameterRows, row -> row.row = "55");;
row116Record := First(ParameterRows, row -> row.row = "116");;
row55Subgroup := ParameterPrescribedSubgroup(row55Record);;
row116Subgroup := ParameterPrescribedSubgroup(row116Record);;

for prescribedSubgroup in [row55Subgroup, row116Subgroup] do
    RequireEqual("order of a parameter-built prescribed normal subgroup",
        Size(prescribedSubgroup), 27);
    RequireEqual("centre of a parameter-built prescribed normal subgroup",
        Size(Centre(prescribedSubgroup)), 3);
    RequireEqual("exponent of a parameter-built prescribed normal subgroup",
        Exponent(prescribedSubgroup), 3);
    RequireEqual("endomorphism-algebra dimension of a parameter-built subgroup",
        Length(MTX.BasisModuleEndomorphisms(GModuleByMats(
            GeneratorsOfGroup(prescribedSubgroup), baseField))), 18);
od;

row55Conjugator := PrescribedSubgroupConjugator(
    row55Subgroup, order27Subgroup);;
row116Conjugator := PrescribedSubgroupConjugator(
    row116Subgroup, order27Subgroup);;
RequireEqual("row-55 prescribed normal subgroup conjugator exists",
    row55Conjugator <> fail, true);
RequireEqual("row-116 prescribed normal subgroup conjugator exists",
    row116Conjugator <> fail, true);
RequireEqual("the standard realization is the row-116 subgroup",
    row116Subgroup, order27Subgroup);
RequireEqual("row-55 subgroup maps onto the standard subgroup",
    row55Subgroup ^ row55Conjugator, order27Subgroup);
RequireEqual("row-116 subgroup maps onto the standard subgroup",
    row116Subgroup ^ row116Conjugator, order27Subgroup);

# 8. Exact comparison of the nine lifts with the row-3 groups.

# Every lift satisfying the five conditions above has O_3 of order 243.  Align
# that subgroup with Ecore, compare the quotient subgroup in Q, lift a quotient
# conjugator, and require equality of the original 18-dimensional matrix groups.

order27MatchIndices := [];;
order27MatchingConjugators := [];;
for G in order27QualifyingGroups do
    O3 := PCore(G, 3);
    x := PrescribedSubgroupConjugator(O3, Ecore);
    RequireEqual("the O_3 alignment for this lift exists", x <> fail, true);
    alignedOrder27Group := G ^ x;
    RequireEqual("the aligned lift lies in the row-3 normaliser",
        IsSubgroup(N, alignedOrder27Group), true);
    order27Image := Image(quo, alignedOrder27Group);
    order27CandidateIndices := [];
    order27CandidateMatrices := [];
    for j in [1 .. Length(alignedHoltYangGroups)] do
        if Size(alignedOrder27Group) = Size(alignedHoltYangGroups[j]) then
            quotientConjugator := RepresentativeAction(
                Q, order27Image, Image(quo, alignedHoltYangGroups[j]));
            if quotientConjugator <> fail then
                liftedConjugator := PreImagesRepresentative(
                    quo, quotientConjugator);
                if alignedOrder27Group ^ liftedConjugator
                   = alignedHoltYangGroups[j] then
                    fullConjugator := x * liftedConjugator
                                      * line3AlignmentMatrices[j]^-1;
                    if G ^ fullConjugator = holtYangGroups[j] then
                        Add(order27CandidateIndices, j);
                        Add(order27CandidateMatrices, fullConjugator);
                    fi;
                fi;
            fi;
        fi;
    od;
    RequireEqual("the lift has a unique exact row-3 match",
        Length(order27CandidateIndices), 1);
    Add(order27MatchIndices, order27CandidateIndices[1]);
    Add(order27MatchingConjugators, order27CandidateMatrices[1]);
od;

RequireEqual("number of exact row-3 matches from rows 55 and 116",
    Length(order27MatchIndices), Length(order27QualifyingGroups));
RequireEqual("distinct row-3 classes met by rows 55 and 116",
    Length(Set(order27MatchIndices)), 7);
for i in [1 .. Length(order27QualifyingGroups)] do
    RequireEqual("a row-55/116 matching matrix has full rank",
        RankMat(order27MatchingConjugators[i]), 18);
    RequireEqual("row-55/116 exact matrix-group equality",
        order27QualifyingGroups[i] ^ order27MatchingConjugators[i],
        holtYangGroups[order27MatchIndices[i]]);
od;

Print("The two covering overgroups for the order-27 normal subgroup yield nine ",
      "lifts satisfying the five conditions.  Exact matrix equalities identify ",
      "all nine with seven of the 40 classes represented in Line3gps.g.  Thus ",
      "the row-55 and row-116 calculations produce no further class on GF(2)^18.\n");
QUIT_GAP(0);
