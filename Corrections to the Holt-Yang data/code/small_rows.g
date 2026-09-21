# Verification for the 23 Holt--Yang rows with b=1 and e<=4 which are not
# decided by the exact Yang--Vasil'ev--Vdovin estimate.  For every possible
# core the calculation constructs the semilinear normaliser, determines the
# conjugacy classes of maximal solvable subgroups in its scalar quotient and
# checks the recorded projective points directly.

SetPrintFormattingStatus("*stdout*", false);;

SmallRowsCheck := function(description, value, expected)
    if value <> expected then
        Error(description, ": expected ", expected, ", found ", value);
    fi;
end;;

SmallRowsPrimePower := function(e)
    local primes, r, n, value;
    primes := Set(FactorsInt(e));
    if Length(primes) <> 1 then
        Error("e is not a prime power: ", e);
    fi;
    r := primes[1];
    n := 0;
    value := e;
    while value > 1 do
        value := value / r;
        n := n + 1;
    od;
    return rec(r := r, n := n);
end;;

SmallRowsScalarMatrix := function(n, scalar, field)
    local matrix, i;
    matrix := NullMat(n, n, field);
    for i in [1 .. n] do
        matrix[i][i] := scalar;
    od;
    return matrix;
end;;

SmallRowsSlotMatrix := function(field, numberOfFactors, factor, localMatrix)
    local tuples, dimension, matrix, row, tuple, columnEntry, value,
          imageTuple, position;
    tuples := Tuples([0, 1], numberOfFactors);
    dimension := Length(tuples);
    matrix := NullMat(dimension, dimension, field);
    for row in [1 .. dimension] do
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

SmallRowsDihedralPair := function(field)
    local zero, one;
    zero := Zero(field);
    one := One(field);
    return [
        [[one, zero], [zero, -one]],
        [[zero, one], [one, zero]]
    ];
end;;

SmallRowsQuaternionPair := function(field)
    local primeField, zero, one, c0, d0, c, d, first, second;
    primeField := PrimeField(field);
    zero := Zero(field);
    one := One(field);
    first := [[zero, one], [-one, zero]];
    # Choosing c and d in the prime field makes this pair fixed by every
    # field automorphism.  The equation has a solution over every finite
    # field of odd prime order.
    for c0 in Elements(primeField) do
        for d0 in Elements(primeField) do
            c := one * c0;
            d := one * d0;
            if c^2 + d^2 = -one then
                second := [[c, d], [d, -c]];
                return [first, second];
            fi;
        od;
    od;
    Error("no quaternion pair over GF(", Size(field), ")");
end;;

SmallRowsBinaryExtraspecialGenerators := function(field, numberOfFactors, kind)
    local generators, dihedral, quaternion, factor, pair;
    generators := [];
    dihedral := SmallRowsDihedralPair(field);
    if kind = "E-" then
        quaternion := SmallRowsQuaternionPair(field);
    fi;
    for factor in [1 .. numberOfFactors] do
        if kind = "E-" and factor = numberOfFactors then
            pair := quaternion;
        else
            pair := dihedral;
        fi;
        Add(generators, SmallRowsSlotMatrix(field, numberOfFactors,
                                            factor, pair[1]));
        Add(generators, SmallRowsSlotMatrix(field, numberOfFactors,
                                            factor, pair[2]));
    od;
    return generators;
end;;

SmallRowsSymplecticTypeGenerators := function(field, numberOfFactors)
    local generators, dimension, fourthRoot;
    generators := SmallRowsBinaryExtraspecialGenerators(
                      field, numberOfFactors, "E+");
    dimension := 2^numberOfFactors;
    fourthRoot := Z(Size(field))^((Size(field) - 1) / 4);
    Add(generators,
        SmallRowsScalarMatrix(dimension, fourthRoot, field));
    return generators;
end;;

# The symplectic-type group contains extraspecial subgroups of both types.
# Multiplying the last dihedral pair by a scalar square root of -1 changes
# that factor from D_8 to Q_8.
SmallRowsExtraspecialCoresInS := function(field, numberOfFactors)
    local plusGenerators, minusGenerators, dimension, fourthRoot,
          fourthRootMatrix, position;
    plusGenerators := SmallRowsBinaryExtraspecialGenerators(
                          field, numberOfFactors, "E+");
    minusGenerators := ShallowCopy(plusGenerators);
    dimension := 2^numberOfFactors;
    fourthRoot := Z(Size(field))^((Size(field) - 1) / 4);
    fourthRootMatrix := SmallRowsScalarMatrix(
                            dimension, fourthRoot, field);
    for position in [Length(minusGenerators) - 1 ..
                     Length(minusGenerators)] do
        minusGenerators[position] :=
            fourthRootMatrix * minusGenerators[position];
    od;
    return [Group(plusGenerators), Group(minusGenerators)];
end;;

SmallRowsPauliGenerators := function(field, r, numberOfFactors)
    local omega, tuples, dimension, generators, factor, shift, clock,
          row, tuple, imageTuple, position;
    omega := Z(Size(field))^((Size(field) - 1) / r);
    tuples := Tuples([0 .. r - 1], numberOfFactors);
    dimension := Length(tuples);
    generators := [];
    for factor in [1 .. numberOfFactors] do
        shift := NullMat(dimension, dimension, field);
        clock := NullMat(dimension, dimension, field);
        for row in [1 .. dimension] do
            tuple := tuples[row];
            imageTuple := ShallowCopy(tuple);
            imageTuple[factor] := (imageTuple[factor] + 1) mod r;
            position := Position(tuples, imageTuple);
            shift[row][position] := One(field);
            clock[row][row] := omega^tuple[factor];
        od;
        Add(generators, shift);
        Add(generators, clock);
    od;
    return generators;
end;;

SmallRowsCoreGenerators := function(field, e, kind)
    local primePower;
    primePower := SmallRowsPrimePower(e);
    if primePower.r = 2 then
        if kind = "S" then
            return SmallRowsSymplecticTypeGenerators(
                       field, primePower.n);
        fi;
        return SmallRowsBinaryExtraspecialGenerators(
                   field, primePower.n, kind);
    fi;
    return SmallRowsPauliGenerators(
               field, primePower.r, primePower.n);
end;;

SmallRowsMultiplicationMatrix := function(extensionField, baseField,
                                           basis, scalar)
    local degree, matrix, row, column, coefficients;
    degree := Length(basis);
    matrix := NullMat(degree, degree, baseField);
    for row in [1 .. degree] do
        coefficients := Coefficients(basis, basis[row] * scalar);
        for column in [1 .. degree] do
            matrix[row][column] := coefficients[column];
        od;
    od;
    return matrix;
end;;

SmallRowsRestrictMatrix := function(extensionField, baseField, matrix)
    local basis, degree, dimension, result, row, column, block,
          blockRow, blockColumn;
    basis := Basis(extensionField);
    degree := Length(basis);
    dimension := Length(matrix);
    result := NullMat(dimension * degree, dimension * degree, baseField);
    for row in [1 .. dimension] do
        for column in [1 .. dimension] do
            block := SmallRowsMultiplicationMatrix(
                         extensionField, baseField, basis,
                         matrix[row][column]);
            for blockRow in [1 .. degree] do
                for blockColumn in [1 .. degree] do
                    result[(row - 1) * degree + blockRow]
                          [(column - 1) * degree + blockColumn] :=
                        block[blockRow][blockColumn];
                od;
            od;
        od;
    od;
    return result;
end;;

SmallRowsFrobeniusMatrix := function(extensionField, baseField)
    local basis, degree, matrix, row, column, coefficients;
    basis := Basis(extensionField);
    degree := Length(basis);
    matrix := NullMat(degree, degree, baseField);
    for row in [1 .. degree] do
        coefficients := Coefficients(
                            basis, basis[row]^Size(baseField));
        for column in [1 .. degree] do
            matrix[row][column] := coefficients[column];
        od;
    od;
    return matrix;
end;;

SmallRowsRepeatDiagonalBlock := function(block, copies, field)
    local size, matrix, copy, row, column;
    size := Length(block);
    matrix := NullMat(size * copies, size * copies, field);
    for copy in [1 .. copies] do
        for row in [1 .. size] do
            for column in [1 .. size] do
                matrix[(copy - 1) * size + row]
                      [(copy - 1) * size + column] := block[row][column];
            od;
        od;
    od;
    return matrix;
end;;

# Lift the automorphisms of T which fix T cap K^* pointwise.  The kernel of
# conjugation on T is K^* by absolute irreducibility, so attaining
# (q-1)|A0| proves that the resulting group is the full linear normaliser.
SmallRowsLinearNormaliser := function(row)
    local q, extensionField, coreGenerators, core, module, scalarMatrix,
           scalarGroup, scalarIntersection, scalarInCore, pcIsomorphism,
           pcCore, pcScalar, automorphisms, fixedAutomorphisms, pcGenerators,
           sourceMatrices, sourceModule, lifts, automorphism, imageMatrices,
           imageModule, intertwiner, i, linearNormaliser,
           expectedAutomorphisms, extraspecialCores,
           expectedExtraspecialOrder;

    q := row.p^row.a;
    extensionField := GF(q);
    coreGenerators := SmallRowsCoreGenerators(
                          extensionField, row.e, row.kind);
    core := Group(coreGenerators);
    module := GModuleByMats(coreGenerators, extensionField);
    SmallRowsCheck(Concatenation("absolute irreducibility in row ",
                                 String(row.row), row.kind),
                   MTX.IsAbsolutelyIrreducible(module), true);
    SmallRowsCheck(Concatenation("core order in row ",
                                 String(row.row), row.kind),
                   Size(core), row.coreOrder);
    if row.kind = "S" then
        extraspecialCores := SmallRowsExtraspecialCoresInS(
            extensionField, SmallRowsPrimePower(row.e).n);
        expectedExtraspecialOrder := 2 * row.e^2;
        SmallRowsCheck(Concatenation(
            "orders of the two extraspecial cores in row ",
            String(row.row)),
            List(extraspecialCores, Size),
            [expectedExtraspecialOrder, expectedExtraspecialOrder]);
        SmallRowsCheck(Concatenation(
            "types of the two extraspecial cores in row ",
            String(row.row)),
            List(extraspecialCores, group ->
                Number(Elements(group), x -> x^2 = One(group))),
            [row.e^2 + row.e, row.e^2 - row.e]);
        SmallRowsCheck(Concatenation(
            "extraspecial cores lie in the symplectic-type core in row ",
            String(row.row)),
            ForAll(extraspecialCores,
                   group -> IsSubgroup(core, group)), true);
    fi;

    scalarMatrix := SmallRowsScalarMatrix(
                        row.e, Z(q), extensionField);
    scalarGroup := Group([scalarMatrix]);
    scalarIntersection := Intersection(core, scalarGroup);
    SmallRowsCheck(Concatenation("scalar intersection in row ",
                                 String(row.row), row.kind),
                   Size(scalarIntersection), row.scalarIntersectionOrder);
    SmallRowsCheck(Concatenation("cyclic scalar intersection in row ",
                                 String(row.row), row.kind),
                   IsCyclic(scalarIntersection), true);
    SmallRowsCheck(Concatenation("centre of the core in row ",
                                 String(row.row), row.kind),
                   Centre(core), scalarIntersection);
    scalarInCore := First(Elements(scalarIntersection),
                          x -> Order(x) = row.scalarIntersectionOrder);
    if scalarInCore = fail then
        Error("the scalar intersection has no generator of the expected order");
    fi;

    pcIsomorphism := IsomorphismPcGroup(core);
    pcCore := Image(pcIsomorphism);
    automorphisms := AutomorphismGroup(pcCore);
    pcScalar := Image(pcIsomorphism, scalarInCore);
    # A matrix normalising the core centralises every scalar matrix.  We
    # therefore retain precisely the automorphisms fixing this generator.
    fixedAutomorphisms := Stabilizer(
                              automorphisms, pcScalar, OnPoints);
    expectedAutomorphisms := row.linearQuotientOrder;
    SmallRowsCheck(Concatenation("automorphisms fixing the scalar centre in row ",
                                 String(row.row), row.kind),
                   Size(fixedAutomorphisms), expectedAutomorphisms);

    pcGenerators := GeneratorsOfGroup(pcCore);
    sourceMatrices := List(pcGenerators,
        x -> PreImagesRepresentative(pcIsomorphism, x));
    SmallRowsCheck(Concatenation("pc generators recover the core in row ",
                                 String(row.row), row.kind),
                   Group(sourceMatrices) = core, true);
    sourceModule := GModuleByMats(sourceMatrices, extensionField);
    lifts := [];
    for automorphism in GeneratorsOfGroup(fixedAutomorphisms) do
        imageMatrices := List(pcGenerators, x ->
            PreImagesRepresentative(
                pcIsomorphism, Image(automorphism, x)));
        imageModule := GModuleByMats(imageMatrices, extensionField);
        intertwiner := MTX.IsomorphismModules(sourceModule, imageModule);
        if intertwiner = fail or RankMat(intertwiner) <> row.e then
            Error("an automorphism did not lift in row ", row.row,
                  row.kind);
        fi;
        SmallRowsCheck(
            Concatenation("intertwining equations in row ",
                          String(row.row), row.kind),
            ForAll([1 .. Length(sourceMatrices)], i ->
                intertwiner^-1 * sourceMatrices[i] * intertwiner
                    = imageMatrices[i]),
            true);
        Add(lifts, intertwiner);
    od;

    linearNormaliser := Group(Concatenation(
        sourceMatrices, lifts, [scalarMatrix]));
    SmallRowsCheck(Concatenation("linear normaliser order in row ",
                                 String(row.row), row.kind),
                   Size(linearNormaliser),
                   (q - 1) * expectedAutomorphisms);
    SmallRowsCheck(Concatenation("core normal in linear normaliser in row ",
                                 String(row.row), row.kind),
                   IsNormal(linearNormaliser, core), true);

    return rec(
        field := extensionField,
        core := core,
        coreGenerators := sourceMatrices,
        scalarGroup := scalarGroup,
        scalarMatrix := scalarMatrix,
        fixedAutomorphisms := fixedAutomorphisms,
        linearNormaliser := linearNormaliser);
end;;

SmallRowsSemilinearNormaliser := function(row)
    local q, localData, extensionField, baseField, linearGenerators,
           extensionGenerators, reducedLinear, reducedCore, reducedScalar,
           frobenius, semilinear, scalarGroup, quotientMap, quotient;

    q := row.p^row.a;
    localData := SmallRowsLinearNormaliser(row);
    extensionField := localData.field;
    baseField := GF(row.p);
    extensionGenerators := GeneratorsOfGroup(localData.linearNormaliser);
    linearGenerators := List(
        extensionGenerators,
        matrix -> SmallRowsRestrictMatrix(
                      extensionField, baseField, matrix));
    reducedLinear := Group(linearGenerators);
    reducedCore := Group(List(localData.coreGenerators,
        matrix -> SmallRowsRestrictMatrix(
                      extensionField, baseField, matrix)));
    reducedScalar := SmallRowsRestrictMatrix(
        extensionField, baseField, localData.scalarMatrix);
    scalarGroup := Group([reducedScalar]);
    frobenius := SmallRowsRepeatDiagonalBlock(
        SmallRowsFrobeniusMatrix(extensionField, baseField),
        row.e, baseField);
    semilinear := Group(Concatenation(linearGenerators, [frobenius]));

    SmallRowsCheck(Concatenation("faithful restriction in row ",
                                 String(row.row), row.kind),
                   Size(reducedLinear), Size(localData.linearNormaliser));
    SmallRowsCheck(Concatenation("restricted core order in row ",
                                 String(row.row), row.kind),
                   Size(reducedCore), row.coreOrder);
    SmallRowsCheck(Concatenation("restricted scalar group order in row ",
                                 String(row.row), row.kind),
                   Size(scalarGroup), q - 1);
    SmallRowsCheck(Concatenation("Frobenius order in row ",
                                 String(row.row), row.kind),
                   Order(frobenius), row.a);
    SmallRowsCheck(Concatenation("semilinear index in row ",
                                 String(row.row), row.kind),
                   Size(semilinear), row.a * Size(reducedLinear));
    SmallRowsCheck(Concatenation("core normal in semilinear normaliser in row ",
                                 String(row.row), row.kind),
                   IsNormal(semilinear, reducedCore), true);
    SmallRowsCheck(Concatenation("scalars normal in semilinear normaliser in row ",
                                 String(row.row), row.kind),
                   IsNormal(semilinear, scalarGroup), true);
    SmallRowsCheck(Concatenation("linear normaliser normal in semilinear normaliser in row ",
                                 String(row.row), row.kind),
                   IsNormal(semilinear, reducedLinear), true);

    quotientMap := NaturalHomomorphismByNormalSubgroup(
                       semilinear, scalarGroup);
    quotient := Image(quotientMap);
    SmallRowsCheck(Concatenation("kernel of the scalar quotient in row ",
                                 String(row.row), row.kind),
                   Kernel(quotientMap) = scalarGroup, true);
    SmallRowsCheck(Concatenation("scalar quotient order in row ",
                                 String(row.row), row.kind),
                   Size(quotient), row.a * row.linearQuotientOrder);

    return rec(
        baseField := baseField,
        extensionField := extensionField,
        fieldBasis := Basis(extensionField),
        core := reducedCore,
        scalarGroup := scalarGroup,
        extensionGenerators := extensionGenerators,
        restrictedLinearGenerators := linearGenerators,
        frobenius := frobenius,
        semilinear := semilinear,
        quotientMap := quotientMap,
        quotient := quotient);
end;;

SmallRowsMaximalSolvablePreimages := function(data)
    local quotient, permutationIsomorphism, permutationQuotient,
          permutationGroups, quotientGroups, preimages, i;
    quotient := data.quotient;
    if IsSolvableGroup(quotient) then
        quotientGroups := [quotient];
    else
        permutationIsomorphism := IsomorphismPermGroup(quotient);
        if permutationIsomorphism = fail then
            Error("GAP did not find a faithful permutation representation ",
                  "of the scalar quotient");
        fi;
        permutationQuotient := Image(permutationIsomorphism);
        SmallRowsCheck("faithful permutation representation of the scalar quotient",
                       Size(permutationQuotient), Size(quotient));
        permutationGroups :=
            MaximalSolvableSubgroups(permutationQuotient);
        quotientGroups := List(permutationGroups,
            group -> PreImage(permutationIsomorphism, group));
    fi;
    if Length(quotientGroups) = 0 then
        Error("no maximal solvable subgroup was returned");
    fi;
    preimages := List(quotientGroups,
        group -> PreImage(data.quotientMap, group));
    SmallRowsCheck("maximal-solvable groups lie in the scalar quotient",
                   ForAll(quotientGroups,
                          group -> IsSubgroup(quotient, group)), true);
    SmallRowsCheck("all maximal-solvable inverse images are solvable",
                   ForAll(preimages, IsSolvableGroup), true);
    SmallRowsCheck("each inverse image contains the scalar group",
                   ForAll(preimages,
                          group -> IsSubgroup(group, data.scalarGroup)),
                   true);
    SmallRowsCheck("each inverse image contains the prescribed core",
                   ForAll(preimages,
                          group -> IsSubgroup(group, data.core)), true);
    SmallRowsCheck("orders of maximal-solvable inverse images",
        ForAll([1 .. Length(preimages)], i ->
            Size(preimages[i]) = Size(data.scalarGroup)
                                 * Size(quotientGroups[i])), true);
    SmallRowsCheck("images of maximal-solvable inverse images",
        ForAll([1 .. Length(preimages)], i ->
            Image(data.quotientMap, preimages[i]) = quotientGroups[i]),
        true);
    return preimages;
end;;

SmallRowsKVectorToFVector := function(coordinates, data)
    local basis;
    basis := data.fieldBasis;
    return Concatenation(List(coordinates,
        coordinate -> Coefficients(basis, coordinate)));
end;;

SmallRowsFVectorToKVector := function(vector, data)
    local basis, degree, numberOfCoordinates, coordinates, coordinate,
          position, coefficients;
    basis := data.fieldBasis;
    degree := Length(basis);
    if Length(vector) mod degree <> 0 then
        Error("the prime-field vector has the wrong length");
    fi;
    numberOfCoordinates := QuoInt(Length(vector), degree);
    coordinates := [];
    for coordinate in [0 .. numberOfCoordinates - 1] do
        position := coordinate * degree + 1;
        coefficients := vector{[position .. position + degree - 1]};
        Add(coordinates,
            Sum([1 .. degree], i -> coefficients[i] * basis[i]));
    od;
    return coordinates;
end;;

SmallRowsCanonicalKLine := function(vector, data)
    local coordinates, first, factor;
    coordinates := SmallRowsFVectorToKVector(vector, data);
    first := PositionProperty(coordinates, x -> not IsZero(x));
    if first = fail then
        Error("the zero vector does not define a projective point");
    fi;
    factor := coordinates[first]^-1;
    coordinates := List(coordinates, x -> factor * x);
    return SmallRowsKVectorToFVector(coordinates, data);
end;;

# The orbit consists of K-lines, even though the matrices have been restricted
# to the prime field.  Its length is at most |H:C|, never p^d.
SmallRowsProjectiveOrbitLength := function(group, vector, data)
    local target, start, queue, seen, head, generators, generator, image,
          code;
    if not IsSubgroup(group, data.scalarGroup) then
        Error("the projective calculation requires the full scalar group");
    fi;
    target := Size(group) / Size(data.scalarGroup);
    start := SmallRowsCanonicalKLine(vector, data);
    queue := [start];
    code := NumberFFVector(start, Size(data.baseField));
    if code = fail then
        Error("a projective point is not defined over the base field");
    fi;
    seen := NewDictionary(code, true);
    AddDictionary(seen, code, true);
    if target = 1 then
        return 1;
    fi;
    head := 1;
    generators := Filtered(GeneratorsOfGroup(group),
        generator -> not generator in data.scalarGroup);
    while head <= Length(queue) do
        for generator in generators do
            image := SmallRowsCanonicalKLine(
                         queue[head] * generator, data);
            code := NumberFFVector(image, Size(data.baseField));
            if code = fail then
                Error("a projective image is not defined over the base field");
            fi;
            if LookupDictionary(seen, code) = fail then
                AddDictionary(seen, code, true);
                Add(queue, image);
                if Length(queue) > target then
                    Error("a projective orbit is larger than the scalar quotient");
                fi;
                if Length(queue) = target then
                    return target;
                fi;
            fi;
        od;
        head := head + 1;
    od;
    return Length(queue);
end;;

SmallRowsDecodePoint := function(encoded, field)
    return List(encoded, function(exponent)
        if exponent = -1 then
            return Zero(field);
        fi;
        return Z(Size(field))^exponent;
    end);
end;;

SmallRowsHasRecordedPoint := function(group, data, encodedPoints)
    local target, encoded, coordinates, vector;
    target := Size(group) / Size(data.scalarGroup);
    for encoded in encodedPoints do
        coordinates := SmallRowsDecodePoint(
                           encoded, data.extensionField);
        vector := SmallRowsKVectorToFVector(coordinates, data);
        if SmallRowsProjectiveOrbitLength(group, vector, data) = target then
            return true;
        fi;
    od;
    return false;
end;;

SmallRowsRows := [
    rec(row:=26,p:=19,e:=4,a:=1), rec(row:=27,p:=23,e:=4,a:=1),
    rec(row:=29,p:=3,e:=4,a:=3),  rec(row:=30,p:=29,e:=4,a:=1),
    rec(row:=31,p:=31,e:=4,a:=1), rec(row:=32,p:=37,e:=4,a:=1),
    rec(row:=33,p:=41,e:=4,a:=1), rec(row:=34,p:=43,e:=4,a:=1),
    rec(row:=35,p:=47,e:=4,a:=1), rec(row:=36,p:=7,e:=4,a:=2),
    rec(row:=37,p:=53,e:=4,a:=1), rec(row:=38,p:=59,e:=4,a:=1),
    rec(row:=39,p:=61,e:=4,a:=1), rec(row:=40,p:=67,e:=4,a:=1),
    rec(row:=41,p:=71,e:=4,a:=1), rec(row:=43,p:=3,e:=4,a:=4),
    rec(row:=44,p:=11,e:=4,a:=2),

    rec(row:=54,p:=7,e:=3,a:=2),  rec(row:=56,p:=11,e:=3,a:=2),
    rec(row:=57,p:=13,e:=3,a:=2),

    rec(row:=82,p:=19,e:=2,a:=2), rec(row:=83,p:=23,e:=2,a:=2),
    rec(row:=85,p:=3,e:=2,a:=6)
];;

SmallRowsCheck("number of rows left by the fixed-point estimate",
               Length(SmallRowsRows), 23);
SmallRowsCheck("row set",
    Set(List(SmallRowsRows, row -> row.row)),
    Concatenation([26,27], [29..41], [43,44], [54,56,57],
                  [82,83,85]));

SmallRowsCalculations := [];;
for SmallRowsOriginalRow in SmallRowsRows do
    SmallRowsRow := ShallowCopy(SmallRowsOriginalRow);
    SmallRowsQ := SmallRowsRow.p^SmallRowsRow.a;
    SmallRowsRow.d := SmallRowsRow.e * SmallRowsRow.a;
    if SmallRowsRow.e = 3 then
        SmallRowsKinds := ["E3"];
    elif SmallRowsQ mod 4 = 1 then
        SmallRowsKinds := ["S"];
    else
        SmallRowsKinds := ["E+", "E-"];
    fi;
    for SmallRowsKind in SmallRowsKinds do
        SmallRowsCopy := ShallowCopy(SmallRowsRow);
        SmallRowsCopy.kind := SmallRowsKind;
        if SmallRowsCopy.e = 2 then
            if SmallRowsKind = "S" then
                SmallRowsCopy.coreOrder := 16;
                SmallRowsCopy.scalarIntersectionOrder := 4;
                SmallRowsCopy.linearQuotientOrder := 24;
            elif SmallRowsKind = "E+" then
                SmallRowsCopy.coreOrder := 8;
                SmallRowsCopy.scalarIntersectionOrder := 2;
                SmallRowsCopy.linearQuotientOrder := 8;
            else
                SmallRowsCopy.coreOrder := 8;
                SmallRowsCopy.scalarIntersectionOrder := 2;
                SmallRowsCopy.linearQuotientOrder := 24;
            fi;
        elif SmallRowsCopy.e = 3 then
            SmallRowsCopy.coreOrder := 27;
            SmallRowsCopy.scalarIntersectionOrder := 3;
            SmallRowsCopy.linearQuotientOrder := 216;
        else
            if SmallRowsKind = "S" then
                SmallRowsCopy.coreOrder := 64;
                SmallRowsCopy.scalarIntersectionOrder := 4;
                SmallRowsCopy.linearQuotientOrder := 11520;
            elif SmallRowsKind = "E+" then
                SmallRowsCopy.coreOrder := 32;
                SmallRowsCopy.scalarIntersectionOrder := 2;
                SmallRowsCopy.linearQuotientOrder := 1152;
            else
                SmallRowsCopy.coreOrder := 32;
                SmallRowsCopy.scalarIntersectionOrder := 2;
                SmallRowsCopy.linearQuotientOrder := 1920;
            fi;
        fi;
        Add(SmallRowsCalculations, SmallRowsCopy);
    od;
od;

SmallRowsCheck("number of row-and-core calculations",
               Length(SmallRowsCalculations), 32);
SmallRowsCheck("e=2 row-and-core calculations",
               Number(SmallRowsCalculations, row -> row.e = 2), 3);
SmallRowsCheck("e=3 row-and-core calculations",
               Number(SmallRowsCalculations, row -> row.e = 3), 3);
SmallRowsCheck("e=4 row-and-core calculations",
               Number(SmallRowsCalculations, row -> row.e = 4), 26);

# A component is named r<row>_<kind>, with '+' and '-' replaced by p and m.
# In a point, -1 denotes zero and a nonnegative integer n denotes the field
# element Z(q)^n.  The first nonzero coordinate is therefore represented by 0.
SmallRowsRecordedPoints := rec();;
SmallRowsRecordedPoints.r26_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r26_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r27_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r27_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r29_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r29_Em := [[0,12,17,15]];
SmallRowsRecordedPoints.r30_S  := [[0,21,25,16]];
SmallRowsRecordedPoints.r31_Ep := [[0,24,8,6]];
SmallRowsRecordedPoints.r31_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r32_S  := [[0,8,21,30]];
SmallRowsRecordedPoints.r33_S  := [[0,36,12,24]];
SmallRowsRecordedPoints.r34_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r34_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r35_Ep := [[0,10,1,28]];
SmallRowsRecordedPoints.r35_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r36_S  := [[0,20,15,24], [0,37,23,5]];
SmallRowsRecordedPoints.r37_S  := [[0,2,39,31], [0,8,13,44]];
SmallRowsRecordedPoints.r38_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r38_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r39_S  := [[0,22,23,13]];
SmallRowsRecordedPoints.r40_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r40_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r41_Ep := [[0,3,2,1]];
SmallRowsRecordedPoints.r41_Em := [[0,0,0,-1]];
SmallRowsRecordedPoints.r43_S  := [[0,65,1,12]];
SmallRowsRecordedPoints.r44_S  := [[0,71,91,69]];
SmallRowsRecordedPoints.r54_E3 := [[0,1,8]];
SmallRowsRecordedPoints.r56_E3 := [[0,91,69]];
SmallRowsRecordedPoints.r57_E3 := [[0,67,99]];
SmallRowsRecordedPoints.r82_S  := [[0,3]];
SmallRowsRecordedPoints.r83_S  := [[0,2]];
SmallRowsRecordedPoints.r85_S  := [[0,4]];

# Sorted orders in the scalar quotient, in the same 32 cases.
SmallRowsRecordedOrders := rec();;
SmallRowsRecordedOrders.r26_Ep := [1152];
SmallRowsRecordedOrders.r26_Em := [192,320,384];
SmallRowsRecordedOrders.r27_Ep := [1152];
SmallRowsRecordedOrders.r27_Em := [192,320,384];
SmallRowsRecordedOrders.r29_Ep := [3456];
SmallRowsRecordedOrders.r29_Em := [576,960,1152];
SmallRowsRecordedOrders.r30_S  := [320,768,768,1152];
SmallRowsRecordedOrders.r31_Ep := [1152];
SmallRowsRecordedOrders.r31_Em := [192,320,384];
SmallRowsRecordedOrders.r32_S  := [320,768,768,1152];
SmallRowsRecordedOrders.r33_S  := [320,768,768,1152];
SmallRowsRecordedOrders.r34_Ep := [1152];
SmallRowsRecordedOrders.r34_Em := [192,320,384];
SmallRowsRecordedOrders.r35_Ep := [1152];
SmallRowsRecordedOrders.r35_Em := [192,320,384];
SmallRowsRecordedOrders.r36_S  := [640,1536,1536,2304];
SmallRowsRecordedOrders.r37_S  := [320,768,768,1152];
SmallRowsRecordedOrders.r38_Ep := [1152];
SmallRowsRecordedOrders.r38_Em := [192,320,384];
SmallRowsRecordedOrders.r39_S  := [320,768,768,1152];
SmallRowsRecordedOrders.r40_Ep := [1152];
SmallRowsRecordedOrders.r40_Em := [192,320,384];
SmallRowsRecordedOrders.r41_Ep := [1152];
SmallRowsRecordedOrders.r41_Em := [192,320,384];
SmallRowsRecordedOrders.r43_S  := [1280,3072,3072,4608];
SmallRowsRecordedOrders.r44_S  := [640,1536,1536,2304];
SmallRowsRecordedOrders.r54_E3 := [432];
SmallRowsRecordedOrders.r56_E3 := [432];
SmallRowsRecordedOrders.r57_E3 := [432];
SmallRowsRecordedOrders.r82_S  := [48];
SmallRowsRecordedOrders.r83_S  := [48];
SmallRowsRecordedOrders.r85_S  := [144];

SmallRowsRunCalculations := function(calculations)
    local SmallRowsCompleted, SmallRowsRow, SmallRowsData,
          SmallRowsTestCoordinates, SmallRowsTestVector,
          SmallRowsTestScalar, SmallRowsPreimages, SmallRowsOrders,
          SmallRowsKey, SmallRowsPointPool, SmallRowsGroup;
    SmallRowsCompleted := 0;
for SmallRowsRow in calculations do
    Print("row ", SmallRowsRow.row, " ", SmallRowsRow.kind,
          ": constructing the semilinear normaliser\n");
    SmallRowsData := SmallRowsSemilinearNormaliser(SmallRowsRow);
    SmallRowsTestCoordinates := List([1 .. SmallRowsRow.e],
        i -> Zero(SmallRowsData.extensionField));
    SmallRowsTestCoordinates[1] := One(SmallRowsData.extensionField);
    if SmallRowsRow.e > 1 then
        SmallRowsTestCoordinates[2] := Z(Size(
            SmallRowsData.extensionField));
    fi;
    SmallRowsTestVector := SmallRowsKVectorToFVector(
                               SmallRowsTestCoordinates, SmallRowsData);
    SmallRowsCheck(Concatenation("coordinate conversion in row ",
                                 String(SmallRowsRow.row),
                                 SmallRowsRow.kind),
        SmallRowsFVectorToKVector(SmallRowsTestVector, SmallRowsData),
        SmallRowsTestCoordinates);
    SmallRowsCheck(Concatenation("restriction of scalars in row ",
                                 String(SmallRowsRow.row),
                                 SmallRowsRow.kind),
        ForAll([1 .. Length(SmallRowsData.extensionGenerators)], i ->
            SmallRowsTestVector *
                SmallRowsData.restrictedLinearGenerators[i]
            = SmallRowsKVectorToFVector(
                SmallRowsTestCoordinates *
                    SmallRowsData.extensionGenerators[i],
                SmallRowsData)), true);
    SmallRowsCheck(Concatenation("Frobenius action in row ",
                                 String(SmallRowsRow.row),
                                 SmallRowsRow.kind),
        SmallRowsTestVector * SmallRowsData.frobenius,
        SmallRowsKVectorToFVector(
            List(SmallRowsTestCoordinates,
                 x -> x^SmallRowsRow.p), SmallRowsData));
    SmallRowsTestScalar := Z(Size(SmallRowsData.extensionField));
    SmallRowsCheck(Concatenation("canonical K-line representative in row ",
                                 String(SmallRowsRow.row),
                                 SmallRowsRow.kind),
        SmallRowsCanonicalKLine(SmallRowsKVectorToFVector(
            List(SmallRowsTestCoordinates,
                 x -> SmallRowsTestScalar * x), SmallRowsData),
            SmallRowsData),
        SmallRowsCanonicalKLine(SmallRowsTestVector, SmallRowsData));
    SmallRowsPreimages :=
        SmallRowsMaximalSolvablePreimages(SmallRowsData);
    SmallRowsOrders := SortedList(List(SmallRowsPreimages, group ->
        Size(group) / Size(SmallRowsData.scalarGroup)));
    SmallRowsCheck("maximal-solvable inverse images are irreducible",
        ForAll(SmallRowsPreimages, group ->
            MTX.IsIrreducible(GModuleByMats(
                GeneratorsOfGroup(group), SmallRowsData.baseField))), true);
    SmallRowsKey := Concatenation("r", String(SmallRowsRow.row), "_",
        ReplacedString(ReplacedString(SmallRowsRow.kind, "+", "p"),
                       "-", "m"));

    Print("  maximal-solvable quotient orders ", SmallRowsOrders, "\n");

    if not IsBound(SmallRowsRecordedOrders.(SmallRowsKey)) then
        Error("no recorded subgroup orders for ", SmallRowsKey);
    fi;
    SmallRowsCheck(Concatenation(
        "maximal-solvable quotient orders for ", SmallRowsKey),
        SmallRowsOrders, SmallRowsRecordedOrders.(SmallRowsKey));
    if not IsBound(SmallRowsRecordedPoints.(SmallRowsKey)) then
        Error("no recorded projective points for ", SmallRowsKey);
    fi;

    SmallRowsPointPool := SmallRowsRecordedPoints.(SmallRowsKey);
    for SmallRowsGroup in SmallRowsPreimages do
        if not SmallRowsHasRecordedPoint(
                   SmallRowsGroup, SmallRowsData,
                   SmallRowsPointPool) then
            Error("no recorded projective point for row ",
                  SmallRowsRow.row, SmallRowsRow.kind,
                  " and quotient-group order ",
                  Size(SmallRowsGroup) /
                      Size(SmallRowsData.scalarGroup));
        fi;
    od;
    SmallRowsCompleted := SmallRowsCompleted + 1;
od;
    return SmallRowsCompleted;
end;;

SmallRowsCompleted := SmallRowsRunCalculations(SmallRowsCalculations);;
SmallRowsCheck("completed calculations", SmallRowsCompleted, 32);
Print("The 32 row-and-core calculations covering the remaining 23 rows ",
      "are complete; every maximal-solvable inverse image ",
      "has a regular orbit.\n");
QUIT_GAP(0);
