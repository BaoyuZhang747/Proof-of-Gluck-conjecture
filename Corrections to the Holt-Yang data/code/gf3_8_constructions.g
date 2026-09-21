# Constructions for the complete enumeration on GF(3)^8.

# The relevant rows of the Holt--Yang table have a prescribed binary
# symplectic-type subgroup.  Its representation of degree e is first written
# over GF(3^a), then inflated b times and
# restricted to GF(3).  The product e*a*b is eight in every case.

GF38AssertEqual := function(description, value, expected)
    if value <> expected then
        Error(description, ": expected ", expected, ", obtained ", value);
    fi;
end;;

# The two row-113 calculations use the same list of irreducible solvable
# multiplicity groups.  It is computed during the first calculation and then
# retained for the second.
GF38Row113MultiplicityData := fail;;

GF38PrimePower := function(e)
    local primes, r, n, x;
    primes := Set(FactorsInt(e));
    if Length(primes) <> 1 then
        Error("the parameter e = ", e, " is not a prime power");
    fi;
    r := primes[1];
    n := 0;
    x := e;
    while x > 1 do
        x := x / r;
        n := n + 1;
    od;
    return rec(r := r, n := n);
end;;

GF38ScalarMatrix := function(n, scalar, field)
    local matrix, i;
    matrix := NullMat(n, n, field);
    for i in [1 .. n] do
        matrix[i][i] := scalar;
    od;
    return matrix;
end;;

# This matrix acts as localMatrix on one tensor factor and trivially on the
# remaining factors.  The basis is indexed by binary tuples.
GF38TensorFactorMatrix := function(field, numberOfFactors, factor, localMatrix)
    local tuples, dimension, matrix, row, tuple, columnEntry, value, image,
          position;
    tuples := Tuples([0, 1], numberOfFactors);
    dimension := Length(tuples);
    matrix := NullMat(dimension, dimension, field);
    for row in [1 .. dimension] do
        tuple := tuples[row];
        for columnEntry in [0, 1] do
            value := localMatrix[tuple[factor] + 1][columnEntry + 1];
            if value <> Zero(field) then
                image := ShallowCopy(tuple);
                image[factor] := columnEntry;
                position := Position(tuples, image);
                matrix[row][position] := value;
            fi;
        od;
    od;
    return matrix;
end;;

GF38QuaternionPair := function(field)
    local zero, one, minusOne, c, d, first, second;
    zero := Zero(field);
    one := One(field);
    minusOne := -one;
    first := [[zero, one], [minusOne, zero]];
    for c in Elements(field) do
        for d in Elements(field) do
            if c^2 + d^2 = minusOne then
                second := [[c, d], [d, -c]];
                return [first, second];
            fi;
        od;
    od;
    Error("no quaternion representation exists over GF(", Size(field), ")");
end;;

GF38DihedralPair := function(field)
    local zero, one;
    zero := Zero(field);
    one := One(field);
    return [[[one, zero], [zero, -one]],
            [[zero, one], [one, zero]]];
end;;

# For the plus type every tensor factor is dihedral.  For the minus type the
# last factor is quaternion.
GF38ExtraspecialGenerators := function(field, numberOfFactors, form)
    local generators, dihedral, quaternion, factor, pair;
    generators := [];
    dihedral := GF38DihedralPair(field);
    quaternion := GF38QuaternionPair(field);
    for factor in [1 .. numberOfFactors] do
        if form = "E-" and factor = numberOfFactors then
            pair := quaternion;
        else
            pair := dihedral;
        fi;
        Add(generators, GF38TensorFactorMatrix(field, numberOfFactors,
                                               factor, pair[1]));
        Add(generators, GF38TensorFactorMatrix(field, numberOfFactors,
                                               factor, pair[2]));
    od;
    return generators;
end;;

# The symplectic-type group S is the central product of the plus extraspecial
# group with a cyclic group of order four.
GF38SymplecticGenerators := function(field, numberOfFactors)
    local generators, dimension, fourthRoot;
    generators := GF38ExtraspecialGenerators(field, numberOfFactors, "E+");
    dimension := 2^numberOfFactors;
    fourthRoot := Z(Size(field))^((Size(field) - 1) / 4);
    Add(generators, GF38ScalarMatrix(dimension, fourthRoot, field));
    return generators;
end;;

GF38CoreGeneratorsOverField := function(q, e, form)
    local data, field;
    data := GF38PrimePower(e);
    if data.r <> 2 then
        Error("only the binary cores occurring on GF(3)^8 are required");
    fi;
    field := GF(q);
    if form = "S" then
        return GF38SymplecticGenerators(field, data.n);
    fi;
    return GF38ExtraspecialGenerators(field, data.n, form);
end;;

GF38MultiplicationMatrix := function(extensionField, baseField, basis, scalar)
    local degree, matrix, i, j, coefficients;
    degree := Length(basis);
    matrix := NullMat(degree, degree, baseField);
    for i in [1 .. degree] do
        coefficients := Coefficients(basis, basis[i] * scalar);
        for j in [1 .. degree] do
            matrix[i][j] := coefficients[j];
        od;
    od;
    return matrix;
end;;

# Restriction of scalars replaces each entry over the extension field by its
# multiplication matrix over the base field.
GF38RestrictScalars := function(extensionField, baseField, matrix)
    local basis, degree, size, result, i, j, block, r, c;
    basis := Basis(extensionField);
    degree := Length(basis);
    size := Length(matrix);
    result := NullMat(size * degree, size * degree, baseField);
    for i in [1 .. size] do
        for j in [1 .. size] do
            block := GF38MultiplicationMatrix(extensionField, baseField,
                                              basis, matrix[i][j]);
            for r in [1 .. degree] do
                for c in [1 .. degree] do
                    result[(i - 1) * degree + r][(j - 1) * degree + c] :=
                        block[r][c];
                od;
            od;
        od;
    od;
    return result;
end;;

GF38FrobeniusMatrix := function(extensionField, baseField)
    local basis, degree, matrix, i, j, coefficients;
    basis := Basis(extensionField);
    degree := Length(basis);
    matrix := NullMat(degree, degree, baseField);
    for i in [1 .. degree] do
        coefficients := Coefficients(basis,
                                     basis[i]^Size(baseField));
        for j in [1 .. degree] do
            matrix[i][j] := coefficients[j];
        od;
    od;
    return matrix;
end;;

GF38RepeatedBlock := function(block, copies, field)
    local size, matrix, copy, i, j;
    size := Length(block);
    matrix := NullMat(size * copies, size * copies, field);
    for copy in [1 .. copies] do
        for i in [1 .. size] do
            for j in [1 .. size] do
                matrix[(copy - 1) * size + i][(copy - 1) * size + j] :=
                    block[i][j];
            od;
        od;
    od;
    return matrix;
end;;

# These two inflations realise A tensor I_b and I_e tensor B, respectively.
GF38InflateCoreMatrix := function(matrix, b, field)
    local e, result, i, j, k;
    e := Length(matrix);
    result := NullMat(e * b, e * b, field);
    for i in [1 .. e] do
        for j in [1 .. e] do
            for k in [1 .. b] do
                result[(i - 1) * b + k][(j - 1) * b + k] := matrix[i][j];
            od;
        od;
    od;
    return result;
end;;

GF38InflateMultiplicityMatrix := function(matrix, e, b, field)
    local result, i, r, c;
    result := NullMat(e * b, e * b, field);
    for i in [1 .. e] do
        for r in [1 .. b] do
            for c in [1 .. b] do
                result[(i - 1) * b + r][(i - 1) * b + c] := matrix[r][c];
            od;
        od;
    od;
    return result;
end;;

GF38ReducedCore := function(form, e, a, b)
    local extensionField, baseField, generators;
    extensionField := GF(3^a);
    baseField := GF(3);
    generators := List(GF38CoreGeneratorsOverField(3^a, e, form),
                       matrix -> GF38InflateCoreMatrix(matrix, b,
                                                       extensionField));
    if a > 1 then
        generators := List(generators,
                           matrix -> GF38RestrictScalars(extensionField,
                                                        baseField, matrix));
    fi;
    GF38AssertEqual("dimension after restriction of scalars",
                    Length(generators[1]), e * a * b);
    return Group(generators);
end;;

# For b=1 the ambient normaliser prescribed for the row is obtained from the
# local normaliser, together with the field automorphism when a>1.  For a=1
# this is simply the full linear normaliser of the prescribed subgroup.
GF38CoreAndNormaliser := function(form, e, a, b)
    local extensionField, baseField, coreGenerators, coreOverExtension,
          localNormaliser, localTwoCore, localTwoCoreNormaliser, core,
          restrictedLocalTwoCore,
          normaliserGenerators, linearNormaliser, frobenius, fieldGenerator;
    extensionField := GF(3^a);
    baseField := GF(3);
    coreGenerators := GF38CoreGeneratorsOverField(3^a, e, form);
    coreOverExtension := Group(coreGenerators);
    if a = 1 then
        core := GF38ReducedCore(form, e, a, b);
        return rec(core := core,
                   normaliser := Normalizer(GL(e * b, 3), core),
                   localNormaliserOrder := fail);
    fi;
    if b <> 1 then
        Error("this construction applies only when b=1; multiplicity cases are treated separately");
    fi;
    localNormaliser := Normalizer(GL(e, 3^a), coreOverExtension);
    localTwoCore := PCore(localNormaliser, 2);
    localTwoCoreNormaliser := Normalizer(GL(e, 3^a), localTwoCore);
    core := Group(List(coreGenerators,
                       matrix -> GF38RestrictScalars(extensionField,
                                                    baseField, matrix)));
    normaliserGenerators := List(GeneratorsOfGroup(localNormaliser),
        matrix -> GF38RestrictScalars(extensionField, baseField, matrix));
    linearNormaliser := Group(normaliserGenerators);
    frobenius := GF38RepeatedBlock(
        GF38FrobeniusMatrix(extensionField, baseField), e, baseField);
    fieldGenerator := GF38RepeatedBlock(
        GF38MultiplicationMatrix(extensionField, baseField,
                                 Basis(extensionField), Z(3^a)),
        e, baseField);
    Add(normaliserGenerators, frobenius);
    restrictedLocalTwoCore := Group(List(GeneratorsOfGroup(localTwoCore),
        matrix -> GF38RestrictScalars(extensionField, baseField, matrix)));
    return rec(core := core,
               coreOverExtension := coreOverExtension,
               restrictedLocalTwoCore := restrictedLocalTwoCore,
               normaliser := Group(normaliserGenerators),
               linearNormaliser := linearNormaliser,
               localNormaliser := localNormaliser,
               localTwoCore := localTwoCore,
               localTwoCoreNormaliser := localTwoCoreNormaliser,
               localNormaliserOrder := Size(localNormaliser),
               extensionDegree := a,
               fieldGenerator := fieldGenerator,
               frobenius := frobenius);
end;;

# Let C be the irreducible group supplied below.  Its endomorphism algebra is
# a finite field.  The displayed scalar has degree a and therefore identifies
# that field with GF(3^a).  Every element normalising C acts on this field.
# The kernel is contained in the normaliser over GF(3^a), and the image has
# order at most a.  The local normaliser and Frobenius matrix constructed above
# attain this upper bound, so the semilinear group is the full normaliser of C
# over GF(3).
GF38VerifySemilinearNormaliser := function(label, data, normalisedCore,
                                            localNormaliser, a,
                                            localNormaliserOrder,
                                            fullNormaliserOrder)
    local module, endomorphisms, powers;
    if localNormaliser <> data.localNormaliser then
        Error(label, ": the computed local normaliser is not the linear factor");
    fi;
    GF38AssertEqual(Concatenation(label, ": local normaliser order"),
                    Size(localNormaliser),
                    localNormaliserOrder);
    GF38AssertEqual(Concatenation(label, ": restricted linear group order"),
                    Size(data.linearNormaliser), localNormaliserOrder);
    if not IsNormal(data.normaliser, normalisedCore) then
        Error(label, ": the prescribed subgroup is not normal in the ambient group");
    fi;
    module := GModuleByMats(GeneratorsOfGroup(normalisedCore), GF(3));
    if not MTX.IsIrreducible(module) then
        Error(label, ": the module for the prescribed subgroup is reducible");
    fi;
    endomorphisms := SMTX.BasisModuleEndomorphisms(module);
    GF38AssertEqual(Concatenation(label,
                                 ": endomorphism-field dimension"),
                    Length(endomorphisms), a);
    GF38AssertEqual(Concatenation(label, ": field-generator order"),
                    Order(data.fieldGenerator), 3^a - 1);
    powers := List([0 .. a - 1],
                   power -> Flat(data.fieldGenerator^power));
    GF38AssertEqual(Concatenation(label,
                                 ": dimension generated by the field scalar"),
                    RankMat(powers), a);
    if not ForAll(GeneratorsOfGroup(normalisedCore), generator ->
        generator * data.fieldGenerator =
        data.fieldGenerator * generator) then
        Error(label, ": the displayed field does not centralise the prescribed subgroup");
    fi;
    if not IsSubgroup(data.normaliser, data.linearNormaliser) then
        Error(label, ": the restricted linear group is not in the ambient group");
    fi;
    GF38AssertEqual(Concatenation(label, ": Frobenius order"),
                    Order(data.frobenius), a);
    GF38AssertEqual(Concatenation(label, ": semilinear index"),
                    Index(data.normaliser, data.linearNormaliser), a);
    GF38AssertEqual(Concatenation(label, ": full normaliser order"),
                    Size(data.normaliser), fullNormaliserOrder);
    GF38AssertEqual(Concatenation(label,
                                 ": semilinear normaliser upper bound"),
                    a * localNormaliserOrder, fullNormaliserOrder);
    return rec(core := normalisedCore,
               endomorphismDimension := Length(endomorphisms),
               localNormaliserOrder := localNormaliserOrder,
               fullNormaliserOrder := fullNormaliserOrder);
end;;

# Every subgroup of the quotient is considered.  If the quotient is not
# solvable, all its subgroup classes are first formed and precisely the solvable
# representatives are retained.  The correspondence theorem then supplies the
# matrix groups containing the chosen normal subgroup.
GF38EnumerateQuotient := function(core, normaliser, label)
    local quotientMap, quotient, solvableQuotient, isomorphism, image,
          subgroupClasses, representatives, solvableRepresentatives,
          accepted, representative, subgroup, preimage, group;
    if not IsNormal(normaliser, core) then
        Error(label, ": the prescribed subgroup is not normal in the ambient group");
    fi;
    quotientMap := NaturalHomomorphismByNormalSubgroup(normaliser, core);
    quotient := Image(quotientMap);
    solvableQuotient := IsSolvableGroup(quotient);
    if solvableQuotient then
        isomorphism := IsomorphismPcGroup(quotient);
        image := Image(isomorphism);
        subgroupClasses := ConjugacyClassesSubgroups(image);
        representatives := List(subgroupClasses, Representative);
    else
        isomorphism := fail;
        subgroupClasses := ConjugacyClassesSubgroups(quotient);
        representatives := List(subgroupClasses, Representative);
    fi;
    if solvableQuotient then
        solvableRepresentatives := representatives;
    else
        solvableRepresentatives := Filtered(representatives, IsSolvableGroup);
    fi;
    accepted := [];
    for representative in solvableRepresentatives do
        if isomorphism = fail then
            subgroup := representative;
        else
            subgroup := PreImage(isomorphism, representative);
        fi;
        preimage := PreImage(quotientMap, subgroup);
        group := Group(GeneratorsOfGroup(preimage));
        SetSize(group, Size(preimage));
        if SatisfiesHoltYangCriteria(group, 3, 8) then
            Add(accepted, group);
        fi;
    od;
    Print(label, ": |normal subgroup| = ", Size(core),
          ", |ambient group| = ", Size(normaliser),
          ", |ambient quotient| = ", Size(quotient),
          ", subgroup classes = ", Length(subgroupClasses),
          ", solvable subgroup classes = ", Length(solvableRepresentatives),
          ", qualifying groups = ", Length(accepted), "\n");
    return rec(quotientOrder := Size(quotient),
               subgroupClassCount := Length(subgroupClasses),
               solvableClassCount := Length(solvableRepresentatives),
               accepted := accepted);
end;;

# If the structural extraspecial subgroup E is normal, then after conjugacy it
# is one of the index-two extraspecial subgroups of S.  One representative from
# each ambient-group conjugacy class is treated; the resulting group may have
# a larger 2-core.
GF38EnumerateSymplecticCore := function(data, label)
    local symplecticCore, normaliser, candidates, representatives, candidate,
          result, accepted, subgroupClassCount, solvableClassCount,
          normaliserOrders, quotientOrders, extraspecialNormaliser,
          normaliserResults;
    symplecticCore := data.core;
    normaliser := data.normaliser;
    candidates := Filtered(MaximalSubgroups(symplecticCore), subgroup ->
        Size(subgroup) = Size(symplecticCore) / 2 and
        Size(Centre(subgroup)) = 2 and
        Size(DerivedSubgroup(subgroup)) = 2);
    representatives := [];
    for candidate in candidates do
        if ForAll(representatives, representative ->
            RepresentativeAction(normaliser, representative, candidate) = fail) then
            Add(representatives, candidate);
        fi;
    od;
    accepted := [];
    subgroupClassCount := 0;
    solvableClassCount := 0;
    normaliserOrders := [];
    quotientOrders := [];
    normaliserResults := [];
    for candidate in representatives do
        extraspecialNormaliser := Normalizer(normaliser, candidate);
        result := GF38EnumerateQuotient(candidate, extraspecialNormaliser,
            Concatenation(label, ", extraspecial subgroup of order ",
                          String(Size(candidate))));
        Append(accepted, result.accepted);
        subgroupClassCount := subgroupClassCount + result.subgroupClassCount;
        solvableClassCount := solvableClassCount + result.solvableClassCount;
        Add(normaliserOrders, Size(extraspecialNormaliser));
        Add(quotientOrders, result.quotientOrder);
        Add(normaliserResults,
            rec(normaliserOrder := Size(extraspecialNormaliser),
                quotientOrder := result.quotientOrder,
                subgroupClassCount := result.subgroupClassCount,
                solvableClassCount := result.solvableClassCount,
                qualifyingCount := Length(result.accepted)));
    od;
    return rec(candidateCount := Length(candidates),
               classCount := Length(representatives),
               normaliserOrders := normaliserOrders,
               quotientOrders := quotientOrders,
               normaliserResults := normaliserResults,
               subgroupClassCount := subgroupClassCount,
               solvableClassCount := solvableClassCount,
               accepted := accepted);
end;;

GF38ScalarIntersectionOrder := function(localNormaliser, multiplicityGroup,
                                        e, b, field)
    local count, scalar;
    count := 0;
    for scalar in Elements(field) do
        if scalar <> Zero(field) and
           scalar * IdentityMat(e, field) in localNormaliser and
           scalar * IdentityMat(b, field) in multiplicityGroup then
            count := count + 1;
        fi;
    od;
    return count;
end;;

# Row 113 has multiplicity four.  The IrredSol library gives 108 irreducible
# solvable subgroups of GL(4,3); its four maximal members contain them all.  The
# central product with each maximal member therefore covers every possible
# multiplicity image.
GF38EnumerateRow113 := function(form)
    local field, e, b, coreOverField, localNormaliser, coreGenerators,
          reducedCore, irreducibleGroups, maximalIndices, accepted,
          subgroupClassCount, solvableClassCount, index, multiplicityGroup,
          localGenerators, multiplicityGenerators, localFactor,
          multiplicityFactor, intersectionOrder, normaliser, expectedOrder,
          result, ambient, maximalGroups, firstContainingCounts, groupIndex,
          position, permutationIsomorphism, permutationAmbient,
          maximalPermutationGroups, permutationGroup, witness, localModule,
          reducedModule, localEndomorphisms, reducedEndomorphisms,
          matrixUnits, row, column, matrixUnit,
          generalMultiplicityGroup, generalMultiplicityGenerators,
          generalMultiplicityFactor, fullIntersectionOrder,
          fullNormaliserOrder;
    field := GF(3);
    e := 2;
    b := 4;
    coreOverField := Group(GF38CoreGeneratorsOverField(3, e, form));
    localNormaliser := Normalizer(GL(e, 3), coreOverField);
    coreGenerators := List(GeneratorsOfGroup(coreOverField),
                           matrix -> GF38InflateCoreMatrix(matrix, b, field));
    reducedCore := Group(coreGenerators);

    # The local two-dimensional module is absolutely irreducible.  On four
    # copies its endomorphism algebra has dimension 16.  The sixteen inflated
    # matrix units below are independent and centralise the prescribed
    # extraspecial subgroup, so this
    # algebra is exactly Mat_4(GF(3)); its group of units is GL(4,3).
    localModule := GModuleByMats(GeneratorsOfGroup(coreOverField), field);
    if not MTX.IsIrreducible(localModule) then
        Error("row 113 ", form, ": the local extraspecial-subgroup module is reducible");
    fi;
    localEndomorphisms := SMTX.BasisModuleEndomorphisms(localModule);
    GF38AssertEqual(Concatenation("row 113 ", form,
                                 ": local endomorphism dimension"),
                    Length(localEndomorphisms), 1);
    reducedModule := GModuleByMats(coreGenerators, field);
    reducedEndomorphisms := SMTX.BasisModuleEndomorphisms(reducedModule);
    GF38AssertEqual(Concatenation("row 113 ", form,
                                 ": endomorphism-algebra dimension"),
                    Length(reducedEndomorphisms), 16);
    matrixUnits := [];
    for row in [1 .. b] do
        for column in [1 .. b] do
            matrixUnit := NullMat(b, b, field);
            matrixUnit[row][column] := One(field);
            Add(matrixUnits,
                GF38InflateMultiplicityMatrix(matrixUnit, e, b, field));
        od;
    od;
    GF38AssertEqual(Concatenation("row 113 ", form,
                                 ": rank of the matrix units"),
                    RankMat(List(matrixUnits, Flat)), 16);
    if not ForAll(coreGenerators, coreGenerator ->
        ForAll(matrixUnits, matrix ->
            coreGenerator * matrix = matrix * coreGenerator)) then
        Error("row 113 ", form,
              ": the displayed matrix algebra does not centralise the prescribed extraspecial subgroup");
    fi;

    # If a matrix normalises the repeated extraspecial subgroup, its action on
    # that subgroup is
    # realised by the local normaliser.  Dividing by that local matrix leaves
    # an element of the centraliser just identified with GL(4,3).  Thus the
    # product of the local normaliser and this commuting GL(4,3) is the full
    # normaliser in GL(8,3), not merely a subgroup of the right order.
    localGenerators := List(GeneratorsOfGroup(localNormaliser),
        matrix -> GF38InflateCoreMatrix(matrix, b, field));
    localFactor := Group(localGenerators);
    generalMultiplicityGroup := GL(b, 3);
    generalMultiplicityGenerators :=
        List(GeneratorsOfGroup(generalMultiplicityGroup),
             matrix -> GF38InflateMultiplicityMatrix(matrix, e, b, field));
    generalMultiplicityFactor := Group(generalMultiplicityGenerators);
    GF38AssertEqual(Concatenation("row 113 ", form,
                                 ": commuting GL(4,3) order"),
                    Size(generalMultiplicityFactor), 24261120);
    if not ForAll(localGenerators, localGenerator ->
        ForAll(generalMultiplicityGenerators, multiplicityGenerator ->
            localGenerator * multiplicityGenerator =
            multiplicityGenerator * localGenerator)) then
        Error("row 113 ", form,
              ": the two normaliser factors do not commute");
    fi;
    fullIntersectionOrder :=
        Size(Intersection(localFactor, generalMultiplicityFactor));
    GF38AssertEqual(Concatenation("row 113 ", form,
                                 ": normaliser-factor intersection"),
                    fullIntersectionOrder, 2);
    fullNormaliserOrder := Size(localFactor) *
        Size(generalMultiplicityFactor) / fullIntersectionOrder;
    if GF38Row113MultiplicityData <> fail then
        irreducibleGroups := GF38Row113MultiplicityData.groups;
        maximalIndices := GF38Row113MultiplicityData.maximalIndices;
        firstContainingCounts :=
            GF38Row113MultiplicityData.firstContainingCounts;
    else
        irreducibleGroups := AllIrreducibleSolubleMatrixGroups(
                                Degree, b, Field, field);
        maximalIndices :=
            IndicesMaximalAbsolutelyIrreducibleSolubleMatrixGroups(b, 3);
        GF38AssertEqual("number of irreducible solvable groups in GL(4,3)",
                        Length(irreducibleGroups), 108);
        GF38AssertEqual("maximal irreducible solvable groups in GL(4,3)",
                        maximalIndices, [15, 50, 66, 74]);

        # Work in the faithful action of GL(4,3) on its 81 vectors.  For every
        # library group, GAP finds a conjugate contained in one of the four
        # selected maximal groups.  In
        # ContainedConjugates(G,A,B,true), the third-argument group B is
        # conjugated under G into the second-argument group A.  Assigning a
        # group to the first such maximal group gives the stated partition of
        # all 108 classes.
        ambient := GL(4, 3);
        maximalGroups := irreducibleGroups{maximalIndices};
        permutationIsomorphism := IsomorphismPermGroup(ambient);
        permutationAmbient := Image(permutationIsomorphism);
        GF38AssertEqual("order of the row-113 permutation group",
                        Size(permutationAmbient), Size(ambient));
        GF38AssertEqual("degree of the row-113 permutation action",
                        LargestMovedPoint(permutationAmbient), 81);
        maximalPermutationGroups := List(maximalGroups,
            group -> Image(permutationIsomorphism, group));
        firstContainingCounts := [0, 0, 0, 0];
        for groupIndex in [1 .. Length(irreducibleGroups)] do
            permutationGroup := Image(permutationIsomorphism,
                                      irreducibleGroups[groupIndex]);
            witness := fail;
            position := 1;
            while position <= 4 and witness = fail do
                if IsInt(Size(maximalPermutationGroups[position]) /
                         Size(permutationGroup)) then
                    witness := ContainedConjugates(
                        permutationAmbient,
                        maximalPermutationGroups[position],
                        permutationGroup, true);
                fi;
                if witness = fail then
                    position := position + 1;
                fi;
            od;
            if position > 4 then
                Error("IrredSol group ", groupIndex,
                      " is contained in none of the four row-113 covering groups");
            fi;
            GF38AssertEqual("returned row-113 conjugate",
                            witness[1], permutationGroup ^ witness[2]);
            if not IsSubgroup(maximalPermutationGroups[position],
                              witness[1]) then
                Error("the row-113 containment check failed for IrredSol ",
                      "group ", groupIndex);
            fi;
            firstContainingCounts[position] :=
                firstContainingCounts[position] + 1;
        od;
        GF38AssertEqual(
            "containment partition of the 108 row-113 multiplicity groups",
            firstContainingCounts, [60, 24, 21, 3]);
        GF38Row113MultiplicityData :=
            rec(groups := irreducibleGroups,
                maximalIndices := maximalIndices,
                firstContainingCounts := firstContainingCounts);
    fi;
    Print("row 113 ", form,
          ": the four maximal irreducible solvable multiplicity groups contain ",
          firstContainingCounts, " of the 108 IrredSol classes\n");
    accepted := [];
    subgroupClassCount := 0;
    solvableClassCount := 0;
    for index in maximalIndices do
        multiplicityGroup := irreducibleGroups[index];
        multiplicityGenerators := List(GeneratorsOfGroup(multiplicityGroup),
            matrix -> GF38InflateMultiplicityMatrix(matrix, e, b, field));
        multiplicityFactor := Group(multiplicityGenerators);
        intersectionOrder := GF38ScalarIntersectionOrder(
            localNormaliser, multiplicityGroup, e, b, field);
        normaliser := Group(Concatenation(localGenerators, multiplicityGenerators));
        expectedOrder := Size(localFactor) * Size(multiplicityFactor) /
                         intersectionOrder;
        GF38AssertEqual("order of a row-113 central product",
                        Size(normaliser), expectedOrder);
        if not IsNormal(normaliser, reducedCore) then
            Error("the prescribed row-113 extraspecial subgroup is not normal in a central product");
        fi;
        result := GF38EnumerateQuotient(reducedCore, normaliser,
            Concatenation("row 113 ", form, ", multiplicity group ",
                          String(index)));
        Append(accepted, result.accepted);
        subgroupClassCount := subgroupClassCount + result.subgroupClassCount;
        solvableClassCount := solvableClassCount + result.solvableClassCount;
    od;
    return rec(core := reducedCore,
               localNormaliserOrder := Size(localNormaliser),
               endomorphismAlgebraDimension :=
                   Length(reducedEndomorphisms),
               commutingGeneralLinearOrder :=
                   Size(generalMultiplicityFactor),
               normaliserIntersectionOrder := fullIntersectionOrder,
               fullNormaliserOrder := fullNormaliserOrder,
               multiplicityContainmentCounts := firstContainingCounts,
               subgroupClassCount := subgroupClassCount,
               solvableClassCount := solvableClassCount,
               accepted := accepted);
end;;
