# Row 2 of the Holt--Yang table: the symplectic-type group on GF(5)^16.
#
# The calculation constructs the group S of order 1024 and proves that the
# quotient of its full linear normaliser by S is Sp(8,2).  Sixteen explicit
# solvable subgroups cover all possibilities that must be considered.  Each
# recorded subgroup is reconstructed from its binary matrices and compared
# with the corresponding group constructed in the accompanying file.  It
# then verifies a regular orbit for the full inverse image of every one of
# these sixteen subgroups.
#
# No regular permutation representation of Sp(8,2) is used, and the
# projective points of GF(5)^16 are not enumerated.  For a proposed point v
# and B <= Sp(8,2), regularity for the inverse image of B is checked using
# only the 256 points in the S-orbit of <v> and the elements of B.

SetPrintFormattingStatus("*stdout*", false);;

Row2Check := function(description, value, expected)
    if value <> expected then
        Error(description, ": expected ", expected, ", found ", value);
    fi;
end;;

Row2ScalarMatrix := function(dimension, scalar, field)
    local matrix, position;
    matrix := NullMat(dimension, dimension, field);
    for position in [1 .. dimension] do
        matrix[position][position] := scalar;
    od;
    return matrix;
end;;

# Matrices act on row vectors.  The basis of the tensor product is indexed by
# the binary tuples in the order returned by Tuples([0,1],numberOfFactors).
Row2TensorFactorMatrix := function(field, numberOfFactors, factor,
                                   localMatrix)
    local tuples, matrix, row, tuple, columnEntry, value, imageTuple,
          position;
    tuples := Tuples([0, 1], numberOfFactors);
    matrix := NullMat(Length(tuples), Length(tuples), field);
    for row in [1 .. Length(tuples)] do
        tuple := tuples[row];
        for columnEntry in [0, 1] do
            value := localMatrix[tuple[factor] + 1][columnEntry + 1];
            if not IsZero(value) then
                imageTuple := ShallowCopy(tuple);
                imageTuple[factor] := columnEntry;
                position := Position(tuples, imageTuple);
                matrix[row][position] := value;
            fi;
        od;
    od;
    return matrix;
end;;

Row2ControlledNotMatrix := function(field, numberOfFactors, control, target)
    local tuples, matrix, row, imageTuple, position;
    if control = target then
        Error("the control and target positions must be distinct");
    fi;
    tuples := Tuples([0, 1], numberOfFactors);
    matrix := NullMat(Length(tuples), Length(tuples), field);
    for row in [1 .. Length(tuples)] do
        imageTuple := ShallowCopy(tuples[row]);
        imageTuple[target] := (imageTuple[target] + imageTuple[control]) mod 2;
        position := Position(tuples, imageTuple);
        matrix[row][position] := One(field);
    od;
    return matrix;
end;;

Row2Bits := function(number, length)
    local bits, position;
    bits := [];
    for position in [1 .. length] do
        Add(bits, number mod 2);
        number := QuoInt(number, 2);
    od;
    return bits;
end;;

Row2Field5 := GF(5);;
Row2Field2 := GF(2);;
Row2One5 := One(Row2Field5);;
Row2Zero5 := Zero(Row2Field5);;
Row2One2 := One(Row2Field2);;
Row2I16 := IdentityMat(16, Row2Field5);;
Row2I8 := IdentityMat(8, Row2Field2);;
Row2FourthRoot := Z(5);;
Row2FourthRootMatrix := Row2ScalarMatrix(
    16, Row2FourthRoot, Row2Field5);;

Row2LocalZ := [
    [Row2One5, Row2Zero5],
    [Row2Zero5, -Row2One5]
];;
Row2LocalX := [
    [Row2Zero5, Row2One5],
    [Row2One5, Row2Zero5]
];;
Row2LocalFourier := [
    [Row2One5, Row2One5],
    [Row2One5, -Row2One5]
];;
Row2LocalPhase := [
    [Row2One5, Row2Zero5],
    [Row2Zero5, Row2FourthRoot]
];;

# The eight involutions below generate the central product of four dihedral
# groups of order 8.  Adjoining the scalar of order 4 gives the prescribed
# symplectic-type group S.
Row2ExtraspecialGenerators := [];;
for Row2Factor in [1 .. 4] do
    Add(Row2ExtraspecialGenerators,
        Row2TensorFactorMatrix(Row2Field5, 4, Row2Factor, Row2LocalZ));
    Add(Row2ExtraspecialGenerators,
        Row2TensorFactorMatrix(Row2Field5, 4, Row2Factor, Row2LocalX));
od;
Row2Eplus := Group(Row2ExtraspecialGenerators);;
Row2ScalarGroup := Group([Row2FourthRootMatrix]);;
Row2SGenerators := Concatenation(
    Row2ExtraspecialGenerators, [Row2FourthRootMatrix]);;
Row2S := Group(Row2SGenerators);;

Row2Check("order of the plus-type extraspecial subgroup",
          Size(Row2Eplus), 512);
Row2Check("centre of the plus-type extraspecial subgroup",
          Centre(Row2Eplus), Group([-Row2I16]));
Row2Check("number of involutions in the plus-type extraspecial subgroup",
          Number(Elements(Row2Eplus), element -> Order(element) = 2), 271);
Row2Check("orders of the eight extraspecial generators",
          List(Row2ExtraspecialGenerators, Order),
          ListWithIdenticalEntries(8, 2));
Row2Check("order of the scalar group", Size(Row2ScalarGroup), 4);
Row2Check("order of S", Size(Row2S), 1024);
Row2Check("centre of S", Centre(Row2S), Row2ScalarGroup);
Row2Check("derived subgroup of S", DerivedSubgroup(Row2S),
          Group([-Row2I16]));
Row2Check("exponent of S", Exponent(Row2S), 4);
Row2Check("scalar intersection with the plus-type extraspecial subgroup",
          Intersection(Row2Eplus, Row2ScalarGroup), Group([-Row2I16]));

# Multiplying the last dihedral pair by the central fourth root changes that
# factor to a quaternion group.  Thus S contains both extraspecial types.
Row2MinusGenerators := ShallowCopy(Row2ExtraspecialGenerators);;
for Row2Position in [7, 8] do
    Row2MinusGenerators[Row2Position] :=
        Row2FourthRootMatrix * Row2MinusGenerators[Row2Position];
od;
Row2Eminus := Group(Row2MinusGenerators);;
Row2Check("order of the minus-type extraspecial subgroup",
          Size(Row2Eminus), 512);
Row2Check("centre of the minus-type extraspecial subgroup",
          Centre(Row2Eminus), Group([-Row2I16]));
Row2Check("number of involutions in the minus-type extraspecial subgroup",
          Number(Elements(Row2Eminus), element -> Order(element) = 2), 239);
Row2Check("the plus-type extraspecial subgroup lies in S",
          IsSubgroup(Row2S, Row2Eplus), true);
Row2Check("the minus-type extraspecial subgroup lies in S",
          IsSubgroup(Row2S, Row2Eminus), true);
Row2Check("the plus-type subgroup and C4 generate S",
          Group(Concatenation(Row2ExtraspecialGenerators,
                              [Row2FourthRootMatrix])), Row2S);
Row2Check("the minus-type subgroup and C4 generate S",
          Group(Concatenation(Row2MinusGenerators,
                              [Row2FourthRootMatrix])), Row2S);

Row2CoreModule := GModuleByMats(Row2SGenerators, Row2Field5);;
Row2Check("absolute irreducibility of S",
          MTX.IsAbsolutelyIrreducible(Row2CoreModule), true);
Row2Check("dimension of the endomorphism algebra of S",
          Length(MTX.BasisModuleEndomorphisms(Row2CoreModule)), 1);

Row2CoreWord := function(bits)
    local word, position;
    word := Row2I16;
    for position in [1 .. 8] do
        if bits[position] = 1 then
            word := word * Row2ExtraspecialGenerators[position];
        fi;
    od;
    return word;
end;;

# Each element of S is recorded together with its image in S/Z(S).  This
# table makes every conjugation check below exact and avoids an isomorphism
# test between independently constructed groups.
Row2SElements := [];;
Row2SQuotientVectors := [];;
for Row2Number in [0 .. 255] do
    Row2BitList := Row2Bits(Row2Number, 8);
    Row2Word := Row2CoreWord(Row2BitList);
    for Row2Power in [0 .. 3] do
        Add(Row2SElements, Row2Word * Row2FourthRootMatrix^Row2Power);
        Add(Row2SQuotientVectors,
            List(Row2BitList, entry -> entry * Row2One2));
    od;
od;
Row2Check("number of recorded elements of S", Length(Set(Row2SElements)),
          1024);
Row2Check("recorded elements of S", Set(Row2SElements), Set(Elements(Row2S)));

# A 16 by 16 matrix over GF(5) is encoded by reading its entries in row
# order as base-5 digits.  This is an exact key: two such matrices have the
# same key if and only if they are equal.  In particular, it does not depend
# on GAP's printed representation of a matrix.
Row2MatrixKey := function(matrix)
    local key, place, row, column;
    key := 0;
    place := 1;
    for row in [1 .. 16] do
        for column in [1 .. 16] do
            key := key + IntFFE(matrix[row][column]) * place;
            place := 5 * place;
        od;
    od;
    return key;
end;;
Row2SKeys := List(Row2SElements, Row2MatrixKey);;
Row2Check("distinct exact keys for the recorded elements of S",
          Length(Set(Row2SKeys)), 1024);
Row2SElementPositions := NewDictionary(0, true);;
for Row2Position in [1 .. Length(Row2SElements)] do
    AddDictionary(Row2SElementPositions,
                  Row2SKeys[Row2Position], Row2Position);
od;
Row2Check("lookup positions for the recorded elements of S",
          List(Row2SKeys,
               key -> LookupDictionary(Row2SElementPositions, key)),
          [1 .. Length(Row2SElements)]);

Row2InducedMatrixNamed := function(matrix, matrixName)
    local rows, generatorNumber, generator, image, position;
    rows := [];
    for generatorNumber in [1 .. Length(Row2ExtraspecialGenerators)] do
        generator := Row2ExtraspecialGenerators[generatorNumber];
        image := matrix^-1 * generator * matrix;
        position := LookupDictionary(Row2SElementPositions,
                                     Row2MatrixKey(image));
        if position = fail then
            if image in Row2S then
                Error("the exact element lookup failed for ", matrixName,
                      " on generator ", generatorNumber);
            fi;
            Error(matrixName, " does not normalise S: the image of ",
                  "extraspecial generator ", generatorNumber,
                  " does not belong to S");
        fi;
        Add(rows, Row2SQuotientVectors[position]);
    od;
    return rows;
end;;

Row2InducedMatrix := function(matrix)
    return Row2InducedMatrixNamed(matrix, "the proposed normaliser matrix");
end;;

Row2CommutatorForm := [];;
for Row2First in [1 .. 8] do
    Row2FormRow := [];
    for Row2Second in [1 .. 8] do
        Row2Commutator :=
            Row2ExtraspecialGenerators[Row2First]^-1
            * Row2ExtraspecialGenerators[Row2Second]^-1
            * Row2ExtraspecialGenerators[Row2First]
            * Row2ExtraspecialGenerators[Row2Second];
        if Row2Commutator = Row2I16 then
            Add(Row2FormRow, Zero(Row2Field2));
        elif Row2Commutator = -Row2I16 then
            Add(Row2FormRow, One(Row2Field2));
        else
            Error("a commutator in S is neither I nor -I");
        fi;
    od;
    Add(Row2CommutatorForm, Row2FormRow);
od;
Row2Check("rank of the commutator form", RankMat(Row2CommutatorForm), 8);
Row2Check("alternating commutator form",
          Row2CommutatorForm + TransposedMat(Row2CommutatorForm),
          NullMat(8, 8, Row2Field2));

# An automorphism acting trivially on S/Z(S) can only change each of the
# eight chosen involutions by the central involution.  Nondegeneracy says
# that every one of the 2^8 possible sign patterns is induced by conjugation
# with an element of S.  The following calculation checks this explicitly.
Row2InnerSignVector := function(element)
    local signs, generator, image;
    signs := [];
    for generator in Row2ExtraspecialGenerators do
        image := element^-1 * generator * element;
        if image = generator then
            Add(signs, 0);
        elif image = -generator then
            Add(signs, 1);
        else
            Error("inner conjugation has an unexpected image in S");
        fi;
    od;
    return signs;
end;;
Row2InnerSignVectors := Set(List(Row2SElements, Row2InnerSignVector));;
Row2Check("all central sign changes are inner",
          Row2InnerSignVectors, Set(Tuples([0, 1], 8)));

# Fourier, phase, and controlled-not matrices give explicit lifts of
# symplectic transformations of S/Z(S).
Row2CliffordLifts := [];;
Row2CliffordNames := [];;
for Row2Factor in [1 .. 4] do
    Add(Row2CliffordLifts,
        Row2TensorFactorMatrix(
            Row2Field5, 4, Row2Factor, Row2LocalFourier));
    Add(Row2CliffordNames, Concatenation("Fourier ", String(Row2Factor)));
    Add(Row2CliffordLifts,
        Row2TensorFactorMatrix(
            Row2Field5, 4, Row2Factor, Row2LocalPhase));
    Add(Row2CliffordNames, Concatenation("phase ", String(Row2Factor)));
od;
for Row2Control in [1 .. 4] do
    for Row2Target in [1 .. 4] do
        if Row2Control <> Row2Target then
            Add(Row2CliffordLifts,
                Row2ControlledNotMatrix(
                    Row2Field5, 4, Row2Control, Row2Target));
            Add(Row2CliffordNames,
                Concatenation("CNOT ", String(Row2Control), "->",
                              String(Row2Target)));
        fi;
    od;
od;
Row2Check("number of Clifford lifts", Length(Row2CliffordLifts), 20);
Row2Check("ranks of the Clifford lifts",
          List(Row2CliffordLifts, RankMat),
          ListWithIdenticalEntries(20, 16));
Row2Check("the Clifford lifts normalise S",
          ForAll(Row2CliffordLifts, matrix ->
              ForAll(Row2SGenerators, generator ->
                  matrix^-1 * generator * matrix in Row2S)), true);

Row2QuotientGenerators := List([1 .. Length(Row2CliffordLifts)],
    position -> Row2InducedMatrixNamed(Row2CliffordLifts[position],
                                       Row2CliffordNames[position]));;
Row2Check("ranks of the induced matrices",
          List(Row2QuotientGenerators, RankMat),
          ListWithIdenticalEntries(20, 8));
Row2Check("the induced matrices preserve the commutator form",
          ForAll(Row2QuotientGenerators, matrix ->
              matrix * Row2CommutatorForm * TransposedMat(matrix)
                  = Row2CommutatorForm), true);
Row2Q := Group(Row2QuotientGenerators);;
Row2SymplecticOrder := 2^16 * Product([1 .. 4],
    position -> 2^(2 * position) - 1);;
Row2Check("order formula for Sp(8,2)", Row2SymplecticOrder, 47377612800);
Row2Check("order of the induced symplectic group", Size(Row2Q),
          Row2SymplecticOrder);

# Since the commutator form is nondegenerate, the preceding subgroup of its
# isometry group has the full order of Sp(8,2).  It is therefore Sp(8,2).
# The kernel of the normaliser action on S/Z(S) is exactly S: an element of
# the kernel maps each of the eight chosen involutions to itself times I or
# -I; nondegeneracy of the commutator form makes this central automorphism
# inner.  After multiplying by an element of S, the element centralises S.
# Absolute irreducibility says that this centraliser consists of the nonzero
# scalars, all of which already lie in Z(S).  Thus the matrices constructed
# above generate the full normaliser M and |M|=|S||Sp(8,2)|.
Row2MGenerators := Concatenation(Row2SGenerators, Row2CliffordLifts);;
Row2NormaliserOrder := 1024 * Row2SymplecticOrder;;
Row2Check("order deduced for the full normaliser", Row2NormaliserOrder,
          48514675507200);

# The natural action on the 255 nonzero vectors is faithful.  It is used in
# all subgroup calculations below.
Row2NaturalPoints := Filtered(AsList(Row2Field2^8),
    vector -> vector <> Zero(Row2Field2^8));;
Row2Check("number of nonzero vectors in GF(2)^8",
          Length(Row2NaturalPoints), 255);
Row2NaturalAction := ActionHomomorphism(
    Row2Q, Row2NaturalPoints, OnRight);;
Row2QPermutation := Image(Row2NaturalAction);;
Row2PermutationGenerators := List(Row2QuotientGenerators,
    matrix -> Image(Row2NaturalAction, matrix));;
Row2Check("kernel of the 255-point action", Kernel(Row2NaturalAction),
          TrivialSubgroup(Row2Q));
Row2Check("order of the 255-point action", Size(Row2QPermutation),
          Row2SymplecticOrder);
Row2Check("transitivity on the nonzero vectors",
          IsTransitive(Row2QPermutation, [1 .. 255]), true);
Row2Check("degree of the quotient action",
          LargestMovedPoint(Row2QPermutation), 255);

# Conjugation on the 1024 elements of S gives a faithful permutation action
# of M/C, where C=Z(S).  Its normal subgroup induced by S is S/C.  The map
# from this permutation group to the 255-point copy of Sp(8,2) has kernel
# exactly S/C.  These assertions check the order and kernel of the normaliser
# extension without asking GAP to recognise a 16-dimensional matrix group of
# order 48,514,675,507,200.
Row2ConjugationPermutation := function(matrix)
    local images, element, image, position;
    images := [];
    for element in Row2SElements do
        image := matrix^-1 * element * matrix;
        position := LookupDictionary(Row2SElementPositions,
                                     Row2MatrixKey(image));
        if position = fail then
            Error("a generator of M does not permute the elements of S");
        fi;
        Add(images, position);
    od;
    return PermList(images);
end;;

Row2ConjugationGenerators := List(
    Row2MGenerators, Row2ConjugationPermutation);;
Row2ConjugationGroup := Group(Row2ConjugationGenerators);;
Row2InnerConjugationGroup := Group(
    Row2ConjugationGenerators{[1 .. Length(Row2SGenerators)]});;
Row2Check("order of the inner automorphism group of S",
          Size(Row2InnerConjugationGroup), 256);
Row2Check("order of the conjugation group M/C",
          Size(Row2ConjugationGroup), 256 * Row2SymplecticOrder);

Row2ConjugationImages := Concatenation(
    ListWithIdenticalEntries(Length(Row2SGenerators),
                             One(Row2QPermutation)),
    Row2PermutationGenerators);;
Row2ConjugationToQuotient := GroupHomomorphismByImages(
    Row2ConjugationGroup, Row2QPermutation,
    Row2ConjugationGenerators, Row2ConjugationImages);;
if Row2ConjugationToQuotient = fail then
    Error("conjugation on S did not give the claimed quotient map");
fi;
Row2Check("the conjugation quotient map is a homomorphism",
          IsGroupHomomorphism(Row2ConjugationToQuotient), true);
Row2Check("image of the conjugation quotient map",
          Image(Row2ConjugationToQuotient), Row2QPermutation);
Row2Check("kernel of the conjugation quotient map",
          Kernel(Row2ConjugationToQuotient), Row2InnerConjugationGroup);
Row2Check("quotient of the conjugation group by the inner automorphisms",
          Index(Row2ConjugationGroup, Row2InnerConjugationGroup),
          Row2SymplecticOrder);
Row2Check("normaliser order from the faithful conjugation action",
          Size(Row2ScalarGroup) * Size(Row2ConjugationGroup),
          Row2NormaliserOrder);

# Words in the twenty quotient generators are evaluated in the corresponding
# Clifford lifts.  This gives an exact lift of every quotient element without
# constructing a regular permutation action or calling Normalizer(GL(16,5),S).
Row2FreeGroup := FreeGroup(Length(Row2QuotientGenerators));;
Row2FreeGenerators := GeneratorsOfGroup(Row2FreeGroup);;
Row2PermutationEpimorphism := GroupHomomorphismByImages(
    Row2FreeGroup, Row2QPermutation, Row2FreeGenerators,
    Row2PermutationGenerators);;
Row2Check("image of the permutation epimorphism",
          Image(Row2PermutationEpimorphism), Row2QPermutation);

Row2LiftPermutationElement := function(element)
    local word, lift;
    word := PreImagesRepresentative(Row2PermutationEpimorphism, element);
    if word = fail then
        Error("a permutation element has no word in the chosen generators");
    fi;
    lift := MappedWord(word, Row2FreeGenerators, Row2CliffordLifts);
    return lift;
end;;

# Quotient subgroups used in the verification are specified by generators in
# the natural eight-dimensional representation over GF(2).  Reading the
# sixty-four entries row by row as binary digits gives a compact integer for
# each generator.  These integers describe the actual subgroups to be tested;
# they are not labels for representatives returned by a GAP calculation.
Row2BinaryMatrixCode := function(matrix)
    local code, place, row, column, entry;
    if DimensionsMat(matrix) <> [8, 8] then
        Error("a quotient matrix must have dimensions 8 by 8");
    fi;
    code := 0;
    place := 1;
    for row in [1 .. 8] do
        for column in [1 .. 8] do
            entry := matrix[row][column];
            if entry = Row2One2 then
                code := code + place;
            elif entry <> Zero(Row2Field2) then
                Error("a quotient matrix has an entry outside GF(2)");
            fi;
            place := 2 * place;
        od;
    od;
    return code;
end;;

Row2BinaryMatrixFromCode := function(code)
    local value, matrix, row, column;
    if not IsInt(code) or code < 0 or code >= 2^64 then
        Error("a binary matrix code must be an integer from 0 to 2^64-1");
    fi;
    value := code;
    matrix := NullMat(8, 8, Row2Field2);
    for row in [1 .. 8] do
        for column in [1 .. 8] do
            if value mod 2 = 1 then
                matrix[row][column] := Row2One2;
            fi;
            value := QuoInt(value, 2);
        od;
    od;
    Row2Check("binary quotient-matrix encoding",
              Row2BinaryMatrixCode(matrix), code);
    return matrix;
end;;

Row2QuotientMatrixGroupFromCodes := function(codes)
    local matrices, group;
    if not IsList(codes) or not ForAll(codes, IsInt) then
        Error("the quotient generators must be a list of binary matrix codes");
    fi;
    matrices := List(codes, Row2BinaryMatrixFromCode);
    if Length(matrices) = 0 then
        group := Group([Row2I8]);
    else
        group := Group(matrices);
    fi;
    Row2Check("recorded quotient matrices preserve the commutator form",
        ForAll(matrices, matrix ->
            matrix * Row2CommutatorForm * TransposedMat(matrix)
                = Row2CommutatorForm), true);
    return group;
end;;


Row2CanonicalProjectivePoint := function(vector)
    local position, scalar;
    position := PositionProperty(vector, entry -> not IsZero(entry));
    if position = fail then
        Error("the zero vector does not represent a projective point");
    fi;
    scalar := vector[position]^-1;
    return List(vector, entry -> scalar * entry);
end;;

Row2PointFromIntegers := function(entries)
    local point;
    if not IsList(entries) or Length(entries) <> 16
       or not ForAll(entries, entry -> IsInt(entry)
                                      and entry >= 0 and entry < 5) then
        Error("a recorded projective point must have sixteen entries from 0 to 4");
    fi;
    point := List(entries, entry -> entry * Row2One5);
    if ForAll(point, IsZero) then
        Error("the zero vector does not represent a projective point");
    fi;
    Row2Check("canonical representative of a recorded projective point",
              Row2CanonicalProjectivePoint(point), point);
    return point;
end;;

Row2ProjectiveAction := function(point, matrix)
    return Row2CanonicalProjectivePoint(point * matrix);
end;;

# A canonical projective point is encoded by its sixteen coordinates, read
# as base-5 digits.  The traversal below stores these integers instead of a
# dense 16 by 16 lift for every element of a quotient subgroup.
Row2CanonicalProjectivePointCode := function(canonical)
    local code, place, entry;
    code := 0;
    place := 1;
    for entry in canonical do
        code := code + IntFFE(entry) * place;
        place := 5 * place;
    od;
    return code;
end;;

Row2ProjectivePointCode := function(point)
    return Row2CanonicalProjectivePointCode(
               Row2CanonicalProjectivePoint(point));
end;;

Row2ProjectivePointCoordinatesFromCode := function(code)
    local value, point, position;
    value := code;
    point := [];
    for position in [1 .. 16] do
        Add(point, (value mod 5) * Row2One5);
        value := QuoInt(value, 5);
    od;
    return point;
end;;

Row2ProjectiveImageCode := function(code, matrix)
    return Row2CanonicalProjectivePointCode(Row2ProjectiveAction(
        Row2ProjectivePointCoordinatesFromCode(code), matrix));
end;;

# Let B be a quotient subgroup and H its full inverse image.  The H-stabiliser
# of <v> is C=Z(S) precisely when (i) the S-orbit of <v> has length
# |S:C|=256 and (ii) among all b in B, exactly one chosen lift sends <v> into
# its S-orbit.  No nonidentity element of the scalar group C fixes a nonzero
# vector, so these two conditions say that v has trivial stabiliser in H.
# The test uses at most 256+|B| projective points, rather than the orbit of
# length 256|B|.
Row2PrepareQuotientGroup := function(quotientGroup)
    local quotientGenerators, generatorLifts, elements, parents,
          generatorNumbers, positions, position, generatorPosition,
          nextElement, quotientOrder;
    quotientGenerators := GeneratorsOfGroup(quotientGroup);
    generatorLifts := List(quotientGenerators,
                           Row2LiftPermutationElement);
    Row2Check("quotient actions of the lifted subgroup generators",
        ForAll([1 .. Length(quotientGenerators)], generatorPosition ->
            Image(Row2NaturalAction,
                  Row2InducedMatrix(generatorLifts[generatorPosition]))
                = quotientGenerators[generatorPosition]), true);

    # A breadth-first traversal records one parent edge for every quotient
    # element.  Word lifting is needed only for the subgroup generators.
    elements := [One(quotientGroup)];
    parents := [0];
    generatorNumbers := [0];
    positions := NewDictionary(One(quotientGroup), true);
    AddDictionary(positions, elements[1], 1);
    position := 1;
    while position <= Length(elements) do
        for generatorPosition in [1 .. Length(quotientGenerators)] do
            nextElement := elements[position]
                           * quotientGenerators[generatorPosition];
            if LookupDictionary(positions, nextElement) = fail then
                Add(elements, nextElement);
                Add(parents, position);
                Add(generatorNumbers, generatorPosition);
                AddDictionary(positions, nextElement, Length(elements));
            fi;
        od;
        position := position + 1;
    od;
    Row2Check("number of enumerated quotient elements",
              Length(elements), Size(quotientGroup));
    quotientOrder := Length(elements);
    elements := fail;
    positions := fail;
    CollectGarbage(true);
    return rec(group := quotientGroup,
               order := quotientOrder,
               parents := parents,
               generatorNumbers := generatorNumbers,
               generatorLifts := generatorLifts);
end;;

Row2ProjectiveIntersectionCount := function(quotientData, vector, stopAt)
    local point, coreOrbit, coreOrbitSet, imageCodes, count, position,
          imageCode;
    point := Row2CanonicalProjectivePoint(vector);
    coreOrbit := Orbit(Row2S, point, Row2ProjectiveAction);
    if Length(coreOrbit) <> 256 then
        return rec(coreOrbitLength := Length(coreOrbit), count := 0);
    fi;
    coreOrbitSet := Set(List(coreOrbit, Row2ProjectivePointCode));
    imageCodes := [Row2ProjectivePointCode(point)];
    count := 0;
    for position in [1 .. quotientData.order] do
        if position = 1 then
            imageCode := imageCodes[1];
        else
            imageCode := Row2ProjectiveImageCode(
                imageCodes[quotientData.parents[position]],
                quotientData.generatorLifts[
                    quotientData.generatorNumbers[position]]);
            Add(imageCodes, imageCode);
        fi;
        if imageCode in coreOrbitSet then
            count := count + 1;
            if stopAt <> fail and count >= stopAt then
                return rec(coreOrbitLength := 256, count := count);
            fi;
        fi;
    od;
    return rec(coreOrbitLength := 256, count := count);
end;;

Row2LineGivesRegularVectors := function(quotientData, vector)
    local result;
    result := Row2ProjectiveIntersectionCount(quotientData, vector, 2);
    return result.coreOrbitLength = 256 and result.count = 1;
end;;

# The following four lists record the basis change and the matrices used
# to identify the six-dimensional group of order 1296 with Korhonen's
# restriction-of-scalars construction.
Row2RecordedOrder1296Data := rec(
    basisChange := [32, 16, 8, 4, 2, 1],
    fieldAutomorphism := [3, 2, 12, 8, 48, 32],
    linearNormaliser := [
        [1, 2, 8, 12, 48, 16],
        [48, 16, 3, 1, 12, 4],
        [16, 32, 1, 2, 4, 8],
        [62, 23, 59, 29, 47, 53],
        [30, 39, 27, 45, 21, 42]
    ],
    radical := [
        [2, 3, 12, 4, 16, 32],
        [16, 32, 1, 2, 4, 8]
    ]
);;

Read("gf5_16_row2_constructions.g");;

# Each quotient subgroup is specified by its name, its generating matrices
# in the fixed natural copy of Sp(8,2), and one projective point.
Row2RecordedCoverData := [
    rec(
        name := "S3 wr S4",
        generators := [
            2310487621341807105, 4647750068672397825, 9241395249175069185,
            9241404165123736065, 9241421688489445380, 9241421688523457025,
            9241421688590303490, 9241421688590304002, 9241421688657674753,
            9241439349495824897, 13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 0, 1, 4, 4, 0, 3
        ]
    ),
    rec(
        name := "(5:4) wr S2",
        generators := [
            577588857680175120, 4661313781551596033, 8124722632487862785,
            9241421688523654403, 9241421688574053635
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "B1(1,4)",
        generators := [
            4647719248123134210, 9386630002081040900, 11548507094811484677
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "G_B2(3,1;GSp2(3)) x S3",
        generators := [
            4647750068672397825, 9241390884967354416, 9241395248670777360,
            9241404233910583809, 9241421826029781507, 9241432705803691806,
            9241444911834404670, 13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "17:8",
        generators := [
            3882194939242030823, 16317414230986269300
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "(5:4) x (S3 wr S2)",
        generators := [
            2310487621341807105, 4647750068672397825, 9241404165123736065,
            9241421688523654403, 9241421688574053635, 9241439349495824897,
            13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "(7:6) x S3",
        generators := [
            4647750068672397825, 9241388707973433348, 9241404165006165000,
            9241421688623663109, 13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "pair(S3 wr S2)",
        generators := [
            577588857680175120, 2310487621341807105, 2328537204223377921,
            9241421688489445380, 9241421688489708036
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "pair(GammaL(1,16))",
        generators := [
            2328369820657098816, 9245898855244892673
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "(S3 wr S2) x (S3 wr S2)",
        generators := [
            2310487621341807105, 4647750068672397825, 9241404165123736065,
            9241421688489445380, 9241421688523457025, 9241421688590303490,
            9241421688590304002, 9241421688657674753, 9241439349495824897,
            13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "(S3 wr S2) x (5:4)",
        generators := [
            4661313781551596033, 8124722632487862785, 9241421688489445380,
            9241421688523457025, 9241421688590303490, 9241421688590304002,
            9241421688657674753
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "(5:4) x (5:4)",
        generators := [
            4661313781551596033, 8124722632487862785, 9241421688523654403,
            9241421688574053635
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "S3 x (7:6)",
        generators := [
            595750859716952577, 4647719248123134465, 9241421688590303490,
            9241421688590304002, 9241430433547420161
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "S3 x ((5:4) x S3)",
        generators := [
            4647750068672397825, 9241404216865194497, 9241417428721467905,
            9241421688590303490, 9241421688590304002, 13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    ),
    rec(
        name := "S3 x (S3 wr S3)",
        generators := [
            2310487621341807105, 4647750068672397825, 9241395249175069185,
            9241404165123736065, 9241421688523457025, 9241421688590303490,
            9241421688590304002, 9241421688657674753, 9241439349495824897,
            13871122105527173633
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 0, 1, 4, 4, 0, 3
        ]
    ),
    rec(
        name := "S3 x G_B2(3,1;GSp2(3))",
        generators := [
            1166436754161402369, 2310355424265634305, 4665782128087400961,
            9241421688590303490, 9241421688590304002, 9277450623048745473,
            12129518074990166529, 15329255790183186945
        ],
        point := [
            0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 2, 3, 4, 1, 2, 3
        ]
    )
];;

Row2Check("number of recorded row-2 groups",
          Length(Row2RecordedCoverData), 16);
Row2Check("fields in each recorded row-2 group",
    ForAll(Row2RecordedCoverData, record ->
        Set(RecNames(record)) = ["generators", "name", "point"]), true);

Row2ConstructedCover := Row2ConstructCover();;
Row2Check("number of independently constructed row-2 groups",
          Length(Row2ConstructedCover), 16);
Row2ConstructedNames := List(Row2ConstructedCover, record -> record.name);;
Row2RecordedNames := List(Row2RecordedCoverData, record -> record.name);;
Row2Check("the recorded row-2 groups occur in the required order",
          Row2RecordedNames, Row2ConstructedNames);
Row2Check("the sixteen row-2 group names are distinct",
          Length(Set(Row2RecordedNames)), 16);

for Row2Position in [1 .. 16] do
    Row2RecordedGroup := Row2RecordedCoverData[Row2Position];
    Row2ConstructedGroup := Row2ConstructedCover[Row2Position];
    Row2QuotientGroup := Row2QuotientMatrixGroupFromCodes(
                             Row2RecordedGroup.generators);
    Row2Check(Concatenation("recorded matrices for ",
                            Row2RecordedGroup.name),
              Row2QuotientGroup, Row2ConstructedGroup.matrices.group);
    Row2QuotientData := Row2PrepareQuotientGroup(
                            Image(Row2NaturalAction,
                                  Row2QuotientGroup));
    Row2Check(Concatenation("recorded projective point for ",
                            Row2RecordedGroup.name),
        Row2LineGivesRegularVectors(
            Row2QuotientData,
            Row2PointFromIntegers(Row2RecordedGroup.point)), true);
    Print("Verified ", Row2RecordedGroup.name, ".\n");
    Unbind(Row2QuotientData);
    CollectGarbage(true);
od;

Print("The row-2 calculation is complete: the full inverse image of each ",
      "of the sixteen covering groups has a regular orbit on GF(5)^16.\n");
QUIT_GAP(0);
