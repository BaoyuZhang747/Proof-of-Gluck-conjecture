# Exhaustive calculation for the minus-type extraspecial subgroup E on GF(3)^16.

SetPrintFormattingStatus("*stdout*", false);;
Read("matrix_group_tests.g");;
Read("gf3_16_extraspecial_quotients.g");;
Read("gf3_16_projective_orbits.g");;
Read("gf3_16_extraspecial_minus_generators.g");;
Read("gf3_16_minus_data.g");;

F3 := GF(3);;
F2 := GF(2);;
one3 := One(F3);;
one2 := One(F2);;
I16 := IdentityMat(16, F3);;
coreGens := List(CoreGeneratorMatrices,
    m -> List(m, row -> List(row, x -> x * one3)));;
Ecore := Group(coreGens);;

Assert(0, Size(Ecore) = 512);;
Assert(0, Size(Centre(Ecore)) = 2);;
Assert(0, Set(Elements(Centre(Ecore))) = Set([ I16, -I16 ]));;
Assert(0, Number(Elements(Ecore), x -> Order(x) = 2) = 239);;
Assert(0, MTX.IsIrreducible(GModuleByMats(coreGens, F3)));;
Assert(0, IsSolvableGroup(Ecore));;
Assert(0, not IsMetacyclicSolvableGroup(Ecore));;
coreCentraliser := FullMatrixAlgebraCentralizer(F3, coreGens);;
Assert(0, Dimension(coreCentraliser) = 1);;

# The centraliser consists of the scalars, and every central automorphism of an
# extraspecial group is inner.  Hence the kernel of the normaliser action on
# E/Z(E) is E.  For each generator of the orthogonal quotient, the data give
# both its action on E/Z(E) and a lifting matrix in GL(16,3).  The checks below
# verify the pairing, and these matrices generate the full orthogonal quotient.

GF316Bits8 := function(n)
    local bits, k, power;
    bits := [];;
    for k in [1 .. 8] do
        power := 2^(8 - k);;
        if n >= power then
            Add(bits, 1);;
            n := n - power;
        else
            Add(bits, 0);
        fi;
    od;
    return bits;
end;;

GF316CoreWord := function(bits)
    local word, i;
    word := I16;;
    for i in [1 .. 8] do
        if not IsZero(bits[i]) then
            word := word * coreGens[i];
        fi;
    od;
    return word;
end;;

quotientMats := [];;
quotientBits := [];;
for n in [0 .. 255] do
    bits := GF316Bits8(n);;
    word := GF316CoreWord(bits);;
    Add(quotientMats, word);;
    Add(quotientBits, List(bits, x -> x * one2));;
    Add(quotientMats, -word);;
    Add(quotientBits, List(bits, x -> x * one2));;
od;

GF316InducedMatrix := function(t)
    local columns, j, image, position, rows, r, c;
    columns := [];;
    for j in [1 .. 8] do
        image := t^-1 * coreGens[j] * t;;
        position := Position(quotientMats, image);;
        if position = fail then
            return fail;
        fi;
        Add(columns, quotientBits[position]);
    od;
    rows := [];;
    for r in [1 .. 8] do
        Add(rows, List([1 .. 8], c -> columns[c][r]));
    od;
    return rows;
end;;

actionMatrices := GF316MinusData.actionMatrices;;
lifts := GF316MinusData.liftMatrices;;
Assert(0, Length(actionMatrices) = Length(lifts));;
Assert(0, ForAll([1 .. Length(lifts)], i ->
    TransposedMat(GF316InducedMatrix(lifts[i])) = actionMatrices[i]));;
Assert(0, ForAll([1 .. Length(lifts)], i ->
    ForAll(AsList(F2^8), v ->
        quotientBits[Position(quotientMats,
            lifts[i]^-1 * GF316CoreWord(List(v, IntFFE)) * lifts[i])]
            = v * actionMatrices[i])));;
Q := Group(actionMatrices);;
Assert(0, Size(Q) = 394813440);;

Print("The minus-type extraspecial subgroup E has order 512, and ",
    "the quotient of its normaliser in GL(16,3) by E has order ",
    Size(Q), ".\n");;

freeQ := FreeGroup(Length(actionMatrices));;
freeQGens := GeneratorsOfGroup(freeQ);;
epiQ := GroupHomomorphismByImages(freeQ, Q, freeQGens, actionMatrices);;
Assert(0, epiQ <> fail and Image(epiQ) = Q);;

GF316LiftQElement := function(q)
    local word;
    word := PreImagesRepresentative(epiQ, q);;
    if word = fail then
        Error("a quotient element has no word in the chosen generators");
    fi;
    return MappedWord(word, freeQGens, lifts);
end;;

GF316LiftQSubgroup := function(K)
    local quotientGenerators, liftedGenerators, i;
    quotientGenerators := GeneratorsOfGroup(K);;
    liftedGenerators := List(quotientGenerators, GF316LiftQElement);;
    for i in [1 .. Length(quotientGenerators)] do
        Assert(0, TransposedMat(
            GF316InducedMatrix(liftedGenerators[i])) = quotientGenerators[i]);
    od;
    return Group(Concatenation(coreGens, liftedGenerators));
end;;

screen := GF316QuasiprimitiveQuotients(-1, Q, coreGens,
    GF316LiftQSubgroup, 16771, 16471, 230, 230);;
Print("GO-(8,2) has ", screen.subgroupClassCount,
    " subgroup classes, of which ", screen.solvableClassCount,
    " are solvable.\n");;
Print("The quadratic-form test on invariant subspaces of E/Z(E) retains ",
    screen.correctedCoreNormalCount, " classes; all ", screen.exactCount,
    " are irreducible and quasiprimitive.\n");;

# A vector with nontrivial E-stabiliser cannot be regular for H.  On an
# E/Z(E)-orbit of projective points with trivial stabiliser, the stabiliser in H
# of a representative vector maps isomorphically onto the stabiliser in K=H/E
# of that E/Z(E)-orbit.  Thus H has a regular vector orbit exactly when K has a
# regular orbit on the E/Z(E)-orbits with trivial stabiliser below.

projectiveAction := GF316ProjectiveRegularCoreAction(coreGens,
    actionMatrices, lifts);;
Assert(0, projectiveAction.lineCount = 21523360);;
Assert(0, projectiveAction.projectiveOrbitCount = 87125);;
Assert(0, projectiveAction.regularCoreOrbitCount = 81600);;
Assert(0, Size(projectiveAction.quotientImage) = Size(Q));;
Print("The ", projectiveAction.lineCount,
    " projective points form ", projectiveAction.projectiveOrbitCount,
    " E/Z(E)-orbits; ", projectiveAction.regularCoreOrbitCount,
    " have trivial point stabiliser.\n");;
Print("The induced action on the E/Z(E)-orbits with trivial point ",
    "stabiliser is faithful, with image order ",
    Size(projectiveAction.quotientImage), ".\n");;

regularCount := 0;;
exceptions := [];;
for r in screen.survivors do
    Kimage := Image(projectiveAction.quotientHomomorphism, r.quotient);;
    Assert(0, Size(Kimage) = r.quotientOrder);;
    quotientOrbits := OrbitsDomain(Kimage,
        [1 .. projectiveAction.regularCoreOrbitCount]);;
    regularOrbit := First(quotientOrbits,
        orbit -> Length(orbit) = r.quotientOrder);;
    if regularOrbit = fail then
        Add(exceptions, r);
    else
        regularCount := regularCount + 1;;
        r.regularVector :=
            projectiveAction.regularCoreRepresentatives[regularOrbit[1]];;
    fi;
    Unbind(quotientOrbits);;
od;
Assert(0, regularCount = 230);;
Assert(0, exceptions = []);;
Print("All ", regularCount,
    " minus-type lifts have a regular orbit.\n");;
QUIT_GAP(0);
