# Matrix-group constructions and exact tests for GF(5)^8.

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;
Read("matrix_group_tests.g");

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

ReadRequired := function(path)
    if not IsReadableFile(path) then
        Error("The required input file is missing or unreadable: ", path);
    fi;
    Read(path);
end;;

ReadRequired("gf5_8_normaliser_generators.g");
S := Group(row10SymplecticCoreGenerators);;
N := Group(row10SymplecticCoreNormaliserGenerators);;

# Most groups with a regular orbit are rejected immediately by one of these
# thirty-two points.  The points are the cyclic shifts of four displayed
# vectors.  Failure to find a regular orbit here proves nothing: in that case
# the exhaustive test in matrix_group_tests.g is still made.
CyclicShifts58 := function(entries)
    local shifts, i;
    shifts := [];
    for i in [0 .. Length(entries)-1] do
        Add(shifts, Concatenation(entries{[i+1 .. Length(entries)]},
                                 entries{[1 .. i]}));
    od;
    return shifts;
end;;

regularOrbitTrialVectors58 := Concatenation(
    CyclicShifts58([1,1,1,2,3,4,2,4]),
    CyclicShifts58([1,0,1,2,0,3,4,2]),
    CyclicShifts58([1,2,0,4,3,0,2,1]),
    CyclicShifts58([1,1,2,3,4,0,0,2]));;
regularOrbitTrialVectors58 := List(regularOrbitTrialVectors58,
    v -> One(GF(5)) * v);;

MeetsCriteria58 := function(G)
    local order, v;
    order := Size(G);
    if order <= 5^8-1 then
        for v in regularOrbitTrialVectors58 do
            if Length(Orbit(G, v, OnRight)) = order then
                return false;
            fi;
        od;
    fi;
    return SatisfiesHoltYangCriteria(G, 5, 8);
end;;

# Since S is absolutely irreducible, its linear centraliser consists of the
# four field scalars, all of which lie in S.  Conjugation fixes this scalar
# centre pointwise and preserves the commutator form on S/Z(S).  An automorphism
# acting trivially on S/Z(S) is inner, and C_GL(8,5)(S)=Z(S) lies in S; hence
# the quotient of the normaliser of S in GL(8,5) by S embeds in Sp(6,2), whose order is
# 2^9(2^2-1)(2^4-1)(2^6-1)=1451520.  The constructed N attains this bound;
# this proves that it is the full normaliser without asking GAP to construct
# that very large matrix normaliser.
CheckRow10Structure := function()
    local scalars, extraspecials, module, symplecticOrder;
    RequireEqual("order of S", Size(S), 256);
    RequireEqual("order of Z(S)", Size(Centre(S)), 4);
    RequireEqual("order of [S,S]", Size(DerivedSubgroup(S)), 2);
    RequireEqual("S is normal in N", IsNormal(N, S), true);
    RequireEqual("order of N", Size(N), 371589120);
    module := GModuleByMats(GeneratorsOfGroup(S), GF(5));
    RequireEqual("S is absolutely irreducible",
               MTX.IsAbsolutelyIrreducible(module), true);
    symplecticOrder := 2^9 * Product([1 .. 3], i -> 2^(2*i) - 1);
    RequireEqual("order formula for Sp(6,2)", symplecticOrder, 1451520);
    RequireEqual("order of N/S", Size(Image(
        NaturalHomomorphismByNormalSubgroup(N, S))), symplecticOrder);
    scalars := Group(Z(5) * IdentityMat(8, GF(5)));
    RequireEqual("Z(S) is the scalar subgroup", Centre(S), scalars);
    extraspecials := Filtered(MaximalSubgroups(S),
        E -> Size(E) = 128 and Size(Centre(E)) = 2
             and Size(DerivedSubgroup(E)) = 2);
    RequireEqual("number of extraspecial maximal subgroups of S",
               Length(extraspecials), 64);
    RequireEqual("S=E Z(S) for every extraspecial maximal subgroup",
               ForAll(extraspecials,
                      E -> ClosureGroup(E, Centre(S)) = S), true);
    return extraspecials;
end;;

# For every extraspecial maximal subgroup E found below, S=<E,Z(S)>.  Since
# Z(S) is the scalar group, every matrix normalising E also normalises S.
# Thus the stabiliser of E in the already certified full normaliser of S is
# the full normaliser of E in GL(8,5).
# The structure calculation also checks the corresponding orthogonal-group order
# bounds for the plus and minus types.
Row10ExtraspecialNormalisers := function()
    local extraspecials, remaining, normalisers, os, orb, key;
    extraspecials := CheckRow10Structure();
    remaining := ShallowCopy(extraspecials);
    normalisers := [];
    while Length(remaining) > 0 do
        os := OrbitStabilizer(N, remaining[1], OnPoints);
        orb := Set(os.orbit);
        key := IdGroup(remaining[1]);
        Add(normalisers, rec(E := remaining[1], M := os.stabilizer,
                          orbitLength := Length(orb), id := key));
        remaining := Filtered(remaining, E -> not E in orb);
    od;
    RequireEqual("number of N-orbits of extraspecial subgroups",
               Length(normalisers), 2);
    return normalisers;
end;;

ExtraspecialNormaliserWithId := function(id)
    local result;
    result := First(Row10ExtraspecialNormalisers(), entry -> entry.id = id);
    if result = fail then
        Error("The requested extraspecial type was not found.");
    fi;
    return result;
end;;

SolvableQuotientClasses := function(C, M)
    local hom, Q, toPerm, P, classes;
    hom := NaturalHomomorphismByNormalSubgroup(M, C);
    Q := Image(hom);
    toPerm := IsomorphismPermGroup(Q);
    P := Image(toPerm);
    classes := ConjugacyClassesSubgroups(P);
    if not IsSolvableGroup(P) then
        classes := Filtered(classes,
                            c -> IsSolvableGroup(Representative(c)));
    fi;
    return rec(hom := hom, toPerm := toPerm, classes := classes,
               quotientOrder := Size(Q));
end;;

EnumerateQuotientGroups58 := function(C, M, expectedTotal)
    local qdata, accepted, i, L, lift, G;
    qdata := SolvableQuotientClasses(C, M);
    RequireEqual("number of solvable quotient-subgroup classes",
               Length(qdata.classes), expectedTotal);
    accepted := [];
    for i in [1 .. expectedTotal] do
        L := PreImage(qdata.toPerm, Representative(qdata.classes[i]));
        lift := PreImage(qdata.hom, L);
        G := Group(GeneratorsOfGroup(lift));
        SetSize(G, Size(lift));
        if MeetsCriteria58(G) then Add(accepted, G); fi;
    od;
    return rec(groups := accepted, quotientOrder := qdata.quotientOrder,
               total := expectedTotal);
end;;

PrimePowerData58 := function(e)
    local primes, r, n, x;
    primes := Set(FactorsInt(e));
    if Length(primes) <> 1 then Error("e is not a prime power"); fi;
    r := primes[1];
    n := 0;
    x := e;
    while x > 1 do x := x / r; n := n + 1; od;
    return rec(r := r, n := n);
end;;

ScalarMatrix58 := function(n, alpha, K)
    local A, i;
    A := NullMat(n, n, K);
    for i in [1 .. n] do A[i][i] := alpha; od;
    return A;
end;;

SlotMatrix58 := function(K, n, slot, localMatrix)
    local tuples, A, row, tuple, bit, value, image, pos;
    tuples := Tuples([0, 1], n);
    A := NullMat(Length(tuples), Length(tuples), K);
    for row in [1 .. Length(tuples)] do
        tuple := tuples[row];
        for bit in [0, 1] do
            value := localMatrix[tuple[slot] + 1][bit + 1];
            if value <> Zero(K) then
                image := ShallowCopy(tuple);
                image[slot] := bit;
                pos := Position(tuples, image);
                A[row][pos] := value;
            fi;
        od;
    od;
    return A;
end;;

BinaryCoreMatrices58 := function(K, n)
    local z, o, dihedral, matrices, slot, pair;
    z := Zero(K);
    o := One(K);
    dihedral := [[[o,z],[z,-o]], [[z,o],[o,z]]];
    matrices := [];
    for slot in [1 .. n] do
        pair := dihedral;
        Add(matrices, SlotMatrix58(K, n, slot, pair[1]));
        Add(matrices, SlotMatrix58(K, n, slot, pair[2]));
    od;
    Add(matrices, ScalarMatrix58(2^n,
        Z(Size(K)) ^ ((Size(K) - 1) / 4), K));
    return matrices;
end;;

MultiplicationMatrix58 := function(K, F, basis, alpha)
    local out, i, j, coeffs;
    out := NullMat(Length(basis), Length(basis), F);
    for i in [1 .. Length(basis)] do
        coeffs := Coefficients(basis, basis[i] * alpha);
        for j in [1 .. Length(basis)] do out[i][j] := coeffs[j]; od;
    od;
    return out;
end;;

BlowUpMatrix58 := function(K, F, A)
    local basis, a, out, i, j, block, r, c;
    basis := Basis(K);
    a := Length(basis);
    out := NullMat(Length(A) * a, Length(A) * a, F);
    for i in [1 .. Length(A)] do
        for j in [1 .. Length(A)] do
            block := MultiplicationMatrix58(K, F, basis, A[i][j]);
            for r in [1 .. a] do
                for c in [1 .. a] do
                    out[(i-1)*a+r][(j-1)*a+c] := block[r][c];
                od;
            od;
        od;
    od;
    return out;
end;;

FrobeniusMatrix58 := function(K, F)
    local basis, out, i, j, coeffs;
    basis := Basis(K);
    out := NullMat(Length(basis), Length(basis), F);
    for i in [1 .. Length(basis)] do
        coeffs := Coefficients(basis, basis[i] ^ Size(F));
        for j in [1 .. Length(basis)] do out[i][j] := coeffs[j]; od;
    od;
    return out;
end;;

RepeatBlock58 := function(block, copies, F)
    local a, out, k, i, j;
    a := Length(block);
    out := NullMat(a * copies, a * copies, F);
    for k in [1 .. copies] do
        for i in [1 .. a] do
            for j in [1 .. a] do
                out[(k-1)*a+i][(k-1)*a+j] := block[i][j];
            od;
        od;
    od;
    return out;
end;;

InflateLocal58 := function(A, b, F)
    local e, out, i, j, r;
    e := Length(A);
    out := NullMat(e*b, e*b, F);
    for i in [1 .. e] do
        for j in [1 .. e] do
            for r in [1 .. b] do
                out[(i-1)*b+r][(j-1)*b+r] := A[i][j];
            od;
        od;
    od;
    return out;
end;;

InflateMultiplicity58 := function(B, e, F)
    local b, out, i, r, c;
    b := Length(B);
    out := NullMat(e*b, e*b, F);
    for i in [1 .. e] do
        for r in [1 .. b] do
            for c in [1 .. b] do
                out[(i-1)*b+r][(i-1)*b+c] := B[r][c];
            od;
        od;
    od;
    return out;
end;;

SemilinearCore58 := function(e, a)
    local F, K, basis, localCore, localN, core, linearNormaliser, gens, frob,
          fieldGenerator;
    F := GF(5);
    K := GF(5^a);
    localCore := Group(BinaryCoreMatrices58(K, PrimePowerData58(e).n));
    localN := Normalizer(GL(e, Size(K)), localCore);
    core := Group(List(GeneratorsOfGroup(localCore),
                       A -> BlowUpMatrix58(K, F, A)));
    gens := List(GeneratorsOfGroup(localN),
                 A -> BlowUpMatrix58(K, F, A));
    linearNormaliser := Group(gens);
    frob := RepeatBlock58(FrobeniusMatrix58(K, F), e, F);
    basis := Basis(K);
    fieldGenerator := RepeatBlock58(
        MultiplicationMatrix58(K, F, basis, Z(Size(K))), e, F);
    Add(gens, frob);
    return rec(core := core, linearNormaliser := linearNormaliser,
               N := Group(gens), localCore := localCore,
               localNormaliser := localN, fieldGenerator := fieldGenerator,
               e := e, a := a);
end;;

MultiplicityCore58 := function(e, b)
    local F, localCore, localN, core, localAction, multiplicity,
          multiplicityGenerators, gens, B;
    F := GF(5);
    localCore := Group(BinaryCoreMatrices58(F, PrimePowerData58(e).n));
    localN := Normalizer(GL(e, 5), localCore);
    core := Group(List(GeneratorsOfGroup(localCore),
                       A -> InflateLocal58(A, b, F)));
    gens := List(GeneratorsOfGroup(localN),
                 A -> InflateLocal58(A, b, F));
    localAction := Group(gens);
    multiplicityGenerators := List(GeneratorsOfGroup(GL(b, 5)),
                                   B -> InflateMultiplicity58(B, e, F));
    multiplicity := Group(multiplicityGenerators);
    Append(gens, multiplicityGenerators);
    return rec(core := core, N := Group(gens), localCore := localCore,
               localNormaliser := localN, localAction := localAction,
               multiplicity := multiplicity, e := e, b := b);
end;;

# The prescribed symplectic-type subgroup can be reducible after restriction
# of scalars.  Its local normaliser contains all GF(5^a)-scalars; after field
# reduction this normaliser is irreducible and its endomorphism algebra is the
# displayed copy of GF(5^a).  The prescribed subgroup is recovered
# intrinsically from the 2-core of the local normaliser, and is therefore
# characteristic in it.  Thus the GF(5^a)-linear normaliser of the local
# normaliser is the local normaliser itself.  Every GF(5)-linear matrix
# normalising that group is consequently semilinear.  Adjoining Frobenius
# attains the resulting upper bound of a times the local order.
CertifySemilinearCore58 := function(data, row)
    local twoCore, expectedTwoCoreOrder, intrinsicCore, coreModule, module,
          endomorphisms, fieldPowers, fieldScalars;
    RequireEqual(Concatenation("local prescribed subgroup normal in its computed normaliser ",
                               "for row ", String(row)),
                 IsNormal(data.localNormaliser, data.localCore), true);
    twoCore := PCore(data.localNormaliser, 2);
    if row = 28 then
        expectedTwoCoreOrder := 128;
    elif row = 84 then
        expectedTwoCoreOrder := 64;
    else
        Error("the semilinear certification is not specified for row ", row);
    fi;
    RequireEqual(Concatenation("2-core order of the local normaliser for row ",
                               String(row)),
                 Size(twoCore), expectedTwoCoreOrder);
    intrinsicCore := Group(Filtered(Elements(twoCore),
        g -> g^4 = One(twoCore)));
    RequireEqual(Concatenation("intrinsic prescribed subgroup in the local normaliser ",
                               "for row ", String(row)),
                 intrinsicCore, data.localCore);
    RequireEqual(Concatenation("faithful restriction of the prescribed subgroup for row ",
                               String(row)),
                 Size(data.core), Size(data.localCore));
    coreModule := GModuleByMats(GeneratorsOfGroup(data.core), GF(5));
    RequireEqual(Concatenation("reducible prescribed subgroup for row ",
                               String(row)),
                 MTX.IsIrreducible(coreModule), false);
    RequireEqual(Concatenation("endomorphism-algebra dimension of the prescribed ",
                               "subgroup for row ", String(row)),
                 Length(MTX.BasisModuleEndomorphisms(coreModule)),
                 data.a ^ 2);
    RequireEqual(Concatenation("faithful field reduction for row ",
                               String(row)),
                 Size(data.linearNormaliser), Size(data.localNormaliser));
    RequireEqual(Concatenation("prescribed subgroup normal in the semilinear normaliser for row ",
                               String(row)), IsNormal(data.N, data.core), true);
    RequireEqual(Concatenation("field-reduced local normaliser normal in the ",
                               "semilinear overgroup for row ", String(row)),
                 IsNormal(data.N, data.linearNormaliser), true);
    RequireEqual(Concatenation("semilinear cosets for row ", String(row)),
                 Size(data.N), data.a * Size(data.linearNormaliser));
    module := GModuleByMats(GeneratorsOfGroup(data.linearNormaliser), GF(5));
    RequireEqual(Concatenation("irreducible field-reduced local normaliser for row ",
                               String(row)), MTX.IsIrreducible(module), true);
    endomorphisms := MTX.BasisModuleEndomorphisms(module);
    RequireEqual(Concatenation("endomorphism-field degree of the field-reduced ",
                               "local normaliser for row ",
                               String(row)), Length(endomorphisms), data.a);
    RequireEqual(Concatenation("order of the embedded field generator for row ",
                               String(row)), Order(data.fieldGenerator),
                 5 ^ data.a - 1);
    RequireEqual(Concatenation("embedded field centralises the field-reduced ",
                               "local normaliser for row ",
                               String(row)),
      ForAll(GeneratorsOfGroup(data.linearNormaliser),
             g -> g * data.fieldGenerator = data.fieldGenerator * g), true);
    fieldPowers := List([0 .. data.a - 1],
                        i -> Flat(data.fieldGenerator ^ i));
    RequireEqual(Concatenation("embedded field-algebra dimension for row ",
                               String(row)), RankMat(fieldPowers), data.a);
    fieldScalars := Group(data.fieldGenerator);
    RequireEqual(Concatenation("embedded field scalars lie in the field-reduced ",
                               "local normaliser for row ", String(row)),
                 IsSubgroup(data.linearNormaliser, fieldScalars), true);
    RequireEqual(Concatenation("semilinear group normalises the embedded field for row ",
                               String(row)), IsNormal(data.N, fieldScalars), true);
end;;

# For a repeated absolutely irreducible prescribed subgroup, its endomorphism
# algebra is Mat_b(GF(5)).  Skolem--Noether and the double-centraliser theorem bound the
# full normaliser by the product of the local normaliser and GL(b,5), whose
# intersection is the scalar group.  The explicit factors below attain that
# bound.
CertifyMultiplicityCore58 := function(data, row)
    local localModule, coreModule, endomorphisms, multiplicityAlgebra,
          expectedOrder;
    localModule := GModuleByMats(GeneratorsOfGroup(data.localCore), GF(5));
    RequireEqual(Concatenation("absolutely irreducible local prescribed subgroup for row ",
                               String(row)),
                 MTX.IsAbsolutelyIrreducible(localModule), true);
    RequireEqual(Concatenation("local prescribed subgroup normal in its computed normaliser ",
                               "for row ", String(row)),
                 IsNormal(data.localNormaliser, data.localCore), true);
    RequireEqual(Concatenation("prescribed subgroup normal in the multiplicity normaliser ",
                               "for row ", String(row)),
                 IsNormal(data.N, data.core), true);
    RequireEqual(Concatenation("faithful local action for row ", String(row)),
                 Size(data.localAction), Size(data.localNormaliser));
    RequireEqual(Concatenation("multiplicity GL centralises the prescribed subgroup for row ",
                               String(row)),
      ForAll(GeneratorsOfGroup(data.multiplicity), g ->
        ForAll(GeneratorsOfGroup(data.core), s -> g * s = s * g)), true);
    RequireEqual(Concatenation("commuting tensor factors for row ", String(row)),
      ForAll(GeneratorsOfGroup(data.multiplicity), g ->
        ForAll(GeneratorsOfGroup(data.localAction), h -> g * h = h * g)), true);
    RequireEqual(Concatenation("scalar intersection in the tensor factors for ",
                               "row ", String(row)),
                 Size(Intersection(data.localAction, data.multiplicity)), 4);
    RequireEqual(Concatenation("generation by the two tensor factors for row ",
                               String(row)),
                 ClosureGroup(data.localAction, data.multiplicity), data.N);
    coreModule := GModuleByMats(GeneratorsOfGroup(data.core), GF(5));
    endomorphisms := MTX.BasisModuleEndomorphisms(coreModule);
    RequireEqual(Concatenation("multiplicity endomorphism-algebra dimension ",
                               "for row ", String(row)),
                 Length(endomorphisms), data.b ^ 2);
    multiplicityAlgebra := AlgebraWithOne(
        GF(5), GeneratorsOfGroup(data.multiplicity));
    RequireEqual(Concatenation("explicit multiplicity-algebra dimension for ",
                               "row ", String(row)),
                 Dimension(multiplicityAlgebra), data.b ^ 2);
    expectedOrder := Size(data.localNormaliser) * Size(GL(data.b, 5)) / 4;
    RequireEqual(Concatenation("tensor-product normaliser order for row ",
                               String(row)), Size(data.N), expectedOrder);
end;;

EnumerateSmallerRow := function(row)
    local data, expectedN, expectedClasses, expectedAccepted, targetOrder,
          candidates, reps, E, U, M, qdata, accepted, totalClasses, L,
          lift, G, inv, distinct, distinctInv, scalar;
    if row = 28 then
        data := SemilinearCore58(4, 2);
        expectedN := 552960; expectedClasses := 2223;
        expectedAccepted := 3; targetOrder := 32;
    elif row = 84 then
        data := SemilinearCore58(2, 4);
        expectedN := 59904; expectedClasses := 916;
        expectedAccepted := 0; targetOrder := 8;
    elif row = 118 then
        data := MultiplicityCore58(4, 2);
        expectedN := 5529600; expectedClasses := 3867;
        expectedAccepted := 6; targetOrder := 32;
    else
        Error("unsupported GF(5)^8 row");
    fi;
    RequireEqual(Concatenation("normaliser order for row ", String(row)),
               Size(data.N), expectedN);
    if row in [28,84] then
        CertifySemilinearCore58(data, row);
    else
        CertifyMultiplicityCore58(data, row);
    fi;
    scalar := Z(5) * IdentityMat(8, GF(5));
    RequireEqual(Concatenation("fourth-root scalar lies in the prescribed subgroup for row ",
                             String(row)), scalar in data.core, true);
    candidates := Filtered(MaximalSubgroups(data.core),
        E -> Size(E) = targetOrder and Size(Centre(E)) = 2
             and Size(DerivedSubgroup(E)) = 2);
    reps := [];
    for E in candidates do
        if ForAll(reps, U -> RepresentativeAction(data.N, U, E) = fail) then
            Add(reps, E);
        fi;
    od;
    RequireEqual(Concatenation("extraspecial-subgroup orbits for row ", String(row)),
               Length(reps), 2);
    RequireEqual(Concatenation("prescribed subgroup is generated by E and iI for row ",
                             String(row)),
      ForAll(reps, E -> ClosureGroup(E, Group(scalar)) = data.core), true);
    accepted := [];
    totalClasses := 0;
    for E in reps do
        M := Normalizer(data.N, E);
        RequireEqual(Concatenation("extraspecial subgroup is normal in its ",
                                   "row-specific normaliser for row ",
                                   String(row)), IsNormal(M, E), true);
        qdata := SolvableQuotientClasses(E, M);
        totalClasses := totalClasses + Length(qdata.classes);
        for L in qdata.classes do
            lift := PreImage(qdata.hom,
                     PreImage(qdata.toPerm, Representative(L)));
            G := Group(GeneratorsOfGroup(lift));
            SetSize(G, Size(lift));
            if MeetsCriteria58(G) then Add(accepted, G); fi;
        od;
    od;
    RequireEqual(Concatenation("solvable quotient classes for row ", String(row)),
               totalClasses, expectedClasses);
    RequireEqual(Concatenation("qualifying groups before GL-conjugacy for row ", String(row)),
               Length(accepted), expectedAccepted);
    distinct := [];
    distinctInv := [];
    for G in accepted do
        inv := CharacteristicPolynomialConjugacyInvariant(G);
        if ForAll([1 .. Length(distinct)],
                  i -> distinctInv[i] <> inv
                       or not AreConjugateInGL(G, distinct[i], 5)) then
            Add(distinct, G);
            Add(distinctInv, inv);
        fi;
    od;
    RequireEqual(Concatenation("distinct accepted groups for row ", String(row)),
               Length(distinct), expectedAccepted);
    return distinct;
end;;

CoreConjugator58 := function(source, target)
    local iso, gens, imgs, x;
    iso := IsomorphismGroups(source, target);
    if iso = fail then return fail; fi;
    gens := GeneratorsOfGroup(source);
    imgs := List(gens, g -> Image(iso, g));
    x := MTX.IsomorphismModules(GModuleByMats(gens, GF(5)),
                               GModuleByMats(imgs, GF(5)));
    if x = fail or RankMat(x) <> 8 then return fail; fi;
    if not ForAll([1 .. Length(gens)],
                  i -> x^-1 * gens[i] * x = imgs[i]) then return fail; fi;
    if source ^ x <> target then return fail; fi;
    return x;
end;;

HoltYangLine10InMinusNormaliser := function(groups, minusE, minusM)
    local covered, coreOrders, witnesses, H, O2, candidates, E, x,
          i;
    covered := 0;
    coreOrders := [];
    witnesses := [];
    RequireEqual("isomorphism type of E-", IdGroup(minusE), [128,2327]);
    for H in groups do
        RequireEqual("a Holt--Yang row-10 group satisfies the five conditions",
                   MeetsCriteria58(H), true);
        O2 := PCore(H, 2);
        Add(coreOrders, Size(O2));
        candidates := [];
        if Size(O2) = 128 and IdGroup(O2) = [128, 2327] then
            candidates := [O2];
        elif Size(O2) = 256 then
            candidates := Filtered(MaximalSubgroups(O2),
                E -> Size(E) = 128 and IdGroup(E) = [128, 2327]
                     and IsNormal(H, E));
        fi;
        RequireEqual("a Holt--Yang row-10 group contains a normal E- subgroup",
                   Length(candidates) > 0, true);
        RequireEqual("the selected E- subgroup acts irreducibly",
          MTX.IsIrreducible(GModuleByMats(
              GeneratorsOfGroup(candidates[1]), GF(5))), true);
        x := CoreConjugator58(candidates[1], minusE);
        RequireEqual("explicit conjugator to the prescribed E- subgroup",
                   x <> fail, true);
        RequireEqual("direct equality with the prescribed E- subgroup",
                   candidates[1] ^ x, minusE);
        RequireEqual("conjugated Holt--Yang group lies in N(E-)",
                   IsSubgroup(minusM, H ^ x), true);
        Add(witnesses, x);
        covered := covered + 1;
    od;
    RequireEqual("Holt--Yang row-10 groups in N(E-)", covered, 22);
    for i in [1 .. Length(groups)] do
        RequireEqual("computed row-10 matrix has full rank",
                   RankMat(witnesses[i]), 8);
    od;
    return rec(covered := covered, coreOrders := Collected(coreOrders),
               witnesses := witnesses);
end;;

ExactMatchIndex := function(G, groups, invariants)
    local inv, i;
    inv := CharacteristicPolynomialConjugacyInvariant(G);
    for i in [1 .. Length(groups)] do
        if invariants[i] = inv and AreConjugateInGL(G, groups[i], 5) then
            return i;
        fi;
    od;
    return 0;
end;;
