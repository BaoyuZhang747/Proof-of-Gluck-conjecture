# Explicit constructions of the sixteen solvable quotient groups used for row 2.
#
# Every matrix acts on row vectors.  The calculation in GL(3,4) near the end
# specialises Korhonen's B2 construction with parameters mu=3 and nu=1.
# It reconstructs the resulting six-dimensional group independently of the
# recorded binary matrices.

Row2Zero2 := Zero(Row2Field2);;
Row2BinaryMatrix := function(rows)
    return List(rows, row -> List(row, entry -> entry * Row2One2));
end;;

# A small binary matrix is recorded as one binary integer for each row.  This
# is the form used for the fixed six-dimensional matrices of Korhonen's group
# G_B2(3,1;GSp2(3)).
Row2BinaryRows := function(matrix)
    local dimension, rows, row, column, code;
    dimension := DimensionsMat(matrix)[1];
    if DimensionsMat(matrix) <> [dimension, dimension] then
        Error("only square binary matrices can be recorded by rows");
    fi;
    rows := [];
    for row in [1 .. dimension] do
        code := 0;
        for column in [1 .. dimension] do
            if matrix[row][column] = Row2One2 then
                code := code + 2^(column - 1);
            elif not IsZero(matrix[row][column]) then
                Error("a recorded matrix has an entry outside GF(2)");
            fi;
        od;
        Add(rows, code);
    od;
    return rows;
end;;

Row2BinaryMatrixFromRows := function(rows)
    local dimension, matrix, row, column, code;
    if not IsList(rows) or Length(rows) = 0
       or not ForAll(rows, IsInt) then
        Error("a nonempty list of binary row integers is required");
    fi;
    dimension := Length(rows);
    if not ForAll(rows, code -> code >= 0 and code < 2^dimension) then
        Error("a binary row integer is outside the permitted range");
    fi;
    matrix := NullMat(dimension, dimension, Row2Field2);
    for row in [1 .. dimension] do
        code := rows[row];
        for column in [1 .. dimension] do
            if code mod 2 = 1 then
                matrix[row][column] := Row2One2;
            fi;
            code := QuoInt(code, 2);
        od;
    od;
    Row2Check("binary row encoding", Row2BinaryRows(matrix), rows);
    return matrix;
end;;

Row2CanonicalAlternatingForm := function(dimension)
    local form, position;
    if dimension mod 2 <> 0 then
        Error("an alternating form of full rank must have even dimension");
    fi;
    form := NullMat(dimension, dimension, Row2Field2);
    for position in [1, 3 .. dimension - 1] do
        form[position][position + 1] := Row2One2;
        form[position + 1][position] := Row2One2;
    od;
    return form;
end;;

Row2BlockDiagonalMatrix := function(matrices)
    local dimensions, total, result, first, matrix, row, column;
    dimensions := List(matrices, matrix -> DimensionsMat(matrix)[1]);
    if not ForAll([1 .. Length(matrices)], position ->
           DimensionsMat(matrices[position]) =
               [dimensions[position], dimensions[position]]) then
        Error("every diagonal block must be square");
    fi;
    total := Sum(dimensions);
    result := NullMat(total, total, Row2Field2);
    first := 0;
    for matrix in matrices do
        for row in [1 .. Length(matrix)] do
            for column in [1 .. Length(matrix)] do
                result[first + row][first + column] := matrix[row][column];
            od;
        od;
        first := first + Length(matrix);
    od;
    return result;
end;;

Row2BlockInterchange := function(blockDimension, numberOfBlocks,
                                 firstBlock, secondBlock)
    local dimension, matrix, block, coordinate, imageBlock, row, column;
    if firstBlock = secondBlock
       or not firstBlock in [1 .. numberOfBlocks]
       or not secondBlock in [1 .. numberOfBlocks] then
        Error("two distinct block positions are required");
    fi;
    dimension := blockDimension * numberOfBlocks;
    matrix := NullMat(dimension, dimension, Row2Field2);
    for block in [1 .. numberOfBlocks] do
        if block = firstBlock then
            imageBlock := secondBlock;
        elif block = secondBlock then
            imageBlock := firstBlock;
        else
            imageBlock := block;
        fi;
        for coordinate in [1 .. blockDimension] do
            row := (block - 1) * blockDimension + coordinate;
            column := (imageBlock - 1) * blockDimension + coordinate;
            matrix[row][column] := Row2One2;
        od;
    od;
    return matrix;
end;;

Row2DirectProductMatrices := function(parts)
    local dimensions, generators, factorGenerators, factorGroups, position,
          generator, blocks, other, group, first, second;
    dimensions := List(parts, part -> part.dimension);
    generators := [];
    factorGenerators := [];
    for position in [1 .. Length(parts)] do
        Add(factorGenerators, []);
        for generator in parts[position].generators do
            blocks := [];
            for other in [1 .. Length(parts)] do
                if other = position then
                    Add(blocks, generator);
                else
                    Add(blocks, IdentityMat(dimensions[other], Row2Field2));
                fi;
            od;
            generator := Row2BlockDiagonalMatrix(blocks);
            Add(generators, generator);
            Add(factorGenerators[position], generator);
        od;
    od;
    factorGroups := List(factorGenerators, Group);
    for position in [1 .. Length(parts)] do
        Row2Check("order of an embedded direct factor",
                  Size(factorGroups[position]), Size(parts[position].group));
    od;
    for first in [1 .. Length(parts) - 1] do
        for second in [first + 1 .. Length(parts)] do
            Row2Check("intersection of two embedded direct factors",
                Intersection(factorGroups[first], factorGroups[second]),
                TrivialSubgroup(factorGroups[first]));
            Row2Check("commutation of two embedded direct factors",
                ForAll(factorGenerators[first], firstGenerator ->
                    ForAll(factorGenerators[second], secondGenerator ->
                        firstGenerator * secondGenerator
                          = secondGenerator * firstGenerator)), true);
        od;
    od;
    group := Group(generators);
    Row2Check("order of a constructed direct product", Size(group),
              Product(List(parts, part -> Size(part.group))));
    return rec(
        dimension := Sum(dimensions),
        generators := generators,
        group := group,
        factorGroups := factorGroups);
end;;

Row2WreathProductMatrices := function(part, numberOfBlocks)
    local parts, result, baseGroup, position, factor;
    parts := List([1 .. numberOfBlocks], position -> part);
    result := Row2DirectProductMatrices(parts);
    baseGroup := result.group;
    for position in [1 .. numberOfBlocks - 1] do
        Add(result.generators,
            Row2BlockInterchange(part.dimension, numberOfBlocks,
                                 position, position + 1));
    od;
    result.group := Group(result.generators);
    Row2Check("normal base group in a constructed wreath product",
              IsNormal(result.group, baseGroup), true);
    Row2Check("order of a constructed wreath product", Size(result.group),
              Size(part.group)^numberOfBlocks * Factorial(numberOfBlocks));
    factor := FactorGroup(result.group, baseGroup);
    Row2Check("order of the top group in a constructed wreath product",
              Size(factor), Factorial(numberOfBlocks));
    Row2Check("symmetric top group in a constructed wreath product",
        IsomorphismGroups(factor, SymmetricGroup(numberOfBlocks)) <> fail,
        true);
    result.baseGroup := baseGroup;
    return result;
end;;

Row2BilinearValue := function(first, form, second)
    local product, position, value;
    product := first * form;
    value := Row2Zero2;
    for position in [1 .. Length(first)] do
        value := value + product[position] * second[position];
    od;
    return value;
end;;

Row2AlternatingMatrixFromCoefficients := function(coefficients, dimension)
    local form, number, first, second;
    form := NullMat(dimension, dimension, Row2Field2);
    number := 0;
    for first in [1 .. dimension - 1] do
        for second in [first + 1 .. dimension] do
            number := number + 1;
            form[first][second] := coefficients[number];
            form[second][first] := coefficients[number];
        od;
    od;
    return form;
end;;

Row2InvariantAlternatingForm := function(generators, dimension)
    local pairs, first, second, equations, generator, row, column,
          equation, number, pair, solutions, choices, choice, coefficients,
          position, form;
    pairs := [];
    for first in [1 .. dimension - 1] do
        for second in [first + 1 .. dimension] do
            Add(pairs, [first, second]);
        od;
    od;
    equations := [];
    for generator in generators do
        for row in [1 .. dimension - 1] do
            for column in [row + 1 .. dimension] do
                equation := [];
                for number in [1 .. Length(pairs)] do
                    pair := pairs[number];
                    Add(equation,
                        generator[row][pair[1]]
                            * generator[column][pair[2]]
                        + generator[row][pair[2]]
                            * generator[column][pair[1]]);
                    if pair = [row, column] then
                        equation[number] := equation[number] + Row2One2;
                    fi;
                od;
                Add(equations, equation);
            od;
        od;
    od;
    solutions := NullspaceMat(TransposedMat(equations));
    choices := Tuples([0, 1], Length(solutions));
    for choice in choices do
        coefficients := ListWithIdenticalEntries(Length(pairs), Row2Zero2);
        for position in [1 .. Length(solutions)] do
            if choice[position] = 1 then
                coefficients := coefficients + solutions[position];
            fi;
        od;
        form := Row2AlternatingMatrixFromCoefficients(
                    coefficients, dimension);
        if RankMat(form) = dimension then
            Row2Check("invariance of a calculated alternating form",
                ForAll(generators, generator ->
                    generator * form * TransposedMat(generator) = form),
                true);
            return form;
        fi;
    od;
    Error("no invariant nondegenerate alternating form was found");
end;;

Row2SymplecticBasis := function(form)
    local dimension, vectors, chosen, first, second, basisMatrix;
    dimension := Length(form);
    vectors := Tuples([Row2Zero2, Row2One2], dimension);
    chosen := [];
    while Length(chosen) < dimension do
        first := First(vectors, vector ->
            RankMat(Concatenation(chosen, [vector])) = Length(chosen) + 1
            and ForAll(chosen, previous ->
                IsZero(Row2BilinearValue(vector, form, previous))));
        if first = fail then
            Error("the alternating form has no symplectic basis");
        fi;
        second := First(vectors, vector ->
            ForAll(chosen, previous ->
                IsZero(Row2BilinearValue(vector, form, previous)))
            and Row2BilinearValue(first, form, vector) = Row2One2);
        if second = fail then
            Error("a symplectic partner was not found");
        fi;
        Add(chosen, first);
        Add(chosen, second);
    od;
    basisMatrix := chosen;
    Row2Check("a calculated symplectic basis",
        basisMatrix * form * TransposedMat(basisMatrix),
        Row2CanonicalAlternatingForm(dimension));
    return basisMatrix;
end;;

Row2MatricesInCanonicalSymplecticBasis := function(generators, form)
    local basisMatrix, changed, dimension;
    dimension := Length(form);
    basisMatrix := Row2SymplecticBasis(form);
    changed := List(generators, generator ->
        basisMatrix * generator * basisMatrix^-1);
    Row2Check("canonical alternating form for changed matrices",
        ForAll(changed, generator ->
            generator * Row2CanonicalAlternatingForm(dimension)
                * TransposedMat(generator)
              = Row2CanonicalAlternatingForm(dimension)), true);
    return rec(
        dimension := dimension,
        generators := changed,
        group := Group(changed),
        basisMatrix := basisMatrix);
end;;

Row2CanonicalSymplecticGroup := function(generators)
    local dimension, form;
    dimension := DimensionsMat(generators[1])[1];
    form := Row2InvariantAlternatingForm(generators, dimension);
    return Row2MatricesInCanonicalSymplecticBasis(generators, form);
end;;

Row2PairedMatrices := function(part)
    local dimension, form, position, generators, generator, rawGroup,
          vectors, zeroCount, result;
    dimension := 2 * part.dimension;
    form := NullMat(dimension, dimension, Row2Field2);
    for position in [1 .. part.dimension] do
        form[position][part.dimension + position] := Row2One2;
        form[part.dimension + position][position] := Row2One2;
    od;
    generators := [];
    for generator in part.generators do
        Add(generators, Row2BlockDiagonalMatrix(
            [generator, TransposedMat(generator^-1)]));
    od;
    rawGroup := Group(generators);
    Row2Check("order of a paired group", Size(rawGroup), Size(part.group));
    Row2Check("evaluation form for a paired group",
        ForAll(generators, generator ->
            generator * form * TransposedMat(generator) = form), true);
    vectors := Tuples([Row2Zero2, Row2One2], dimension);
    zeroCount := Number(vectors, vector ->
        IsZero(Sum([1 .. part.dimension], position ->
            vector[position] * vector[part.dimension + position])));
    Row2Check("plus type of the evaluation quadratic form", zeroCount,
        2^(dimension - 1) + 2^(dimension / 2 - 1));
    result := Row2MatricesInCanonicalSymplecticBasis(generators, form);
    result.pairedPartOrder := Size(part.group);
    return result;
end;;

Row2QuadraticValue := function(vector, coefficients)
    local value, position;
    value := Row2Zero2;
    for position in [1, 3 .. Length(vector) - 1] do
        value := value + vector[position] * vector[position + 1];
    od;
    for position in [1 .. Length(vector)] do
        value := value + coefficients[position] * vector[position];
    od;
    return value;
end;;

Row2InvariantQuadraticTypes := function(group)
    local dimension, vectors, choices, generators, types, coefficients,
          zeroCount;
    dimension := DimensionsMat(GeneratorsOfGroup(group)[1])[1];
    vectors := Tuples([Row2Zero2, Row2One2], dimension);
    choices := Tuples([Row2Zero2, Row2One2], dimension);
    generators := GeneratorsOfGroup(group);
    types := [];
    for coefficients in choices do
        if ForAll(generators, generator ->
               ForAll(vectors, vector ->
                   Row2QuadraticValue(vector * generator, coefficients)
                     = Row2QuadraticValue(vector, coefficients))) then
            zeroCount := Number(vectors, vector ->
                IsZero(Row2QuadraticValue(vector, coefficients)));
            if zeroCount = 2^(dimension - 1) + 2^(dimension / 2 - 1) then
                AddSet(types, "plus");
            elif zeroCount =
                    2^(dimension - 1) - 2^(dimension / 2 - 1) then
                AddSet(types, "minus");
            else
                Error("an invariant quadratic form has an unexpected type");
            fi;
        fi;
    od;
    return types;
end;;

Row2CoverEntry := function(name, construction, matrices, order, formType)
    Row2Check(Concatenation("order of ", name), Size(matrices.group), order);
    Row2Check(Concatenation("solvability of ", name),
              IsSolvableGroup(matrices.group), true);
    Row2Check(Concatenation("trivial 2-core of ", name),
              PCore(matrices.group, 2), TrivialSubgroup(matrices.group));
    Row2Check(Concatenation("complete reducibility of ", name),
        Length(MTX.BasisSocle(
            GModuleByMats(matrices.generators, Row2Field2))), 8);
    Row2Check(Concatenation("the fixed alternating form for ", name),
        ForAll(matrices.generators, generator ->
            generator * Row2CanonicalAlternatingForm(8)
                * TransposedMat(generator)
              = Row2CanonicalAlternatingForm(8)), true);
    if formType <> fail then
        Row2Check(Concatenation("quadratic form for ", name),
            formType in Row2InvariantQuadraticTypes(matrices.group), true);
    fi;
    return rec(
        name := name,
        construction := construction,
        matrices := matrices,
        order := order,
        formType := formType);
end;;

Row2RestrictionFromGF4 := function(matrix, omega)
    local zero4, one4, multiplication, result, blockRow, blockColumn,
          small, row, column;
    zero4 := Zero(GF(4));
    one4 := One(GF(4));
    multiplication := function(entry)
        if entry = zero4 then
            return NullMat(2, 2, Row2Field2);
        elif entry = one4 then
            return IdentityMat(2, Row2Field2);
        elif entry = omega then
            return Row2BinaryMatrix([[0, 1], [1, 1]]);
        elif entry = omega^2 then
            return Row2BinaryMatrix([[1, 1], [1, 0]]);
        fi;
        Error("an entry is not in GF(4)");
    end;
    result := NullMat(6, 6, Row2Field2);
    for blockRow in [1 .. 3] do
        for blockColumn in [1 .. 3] do
            small := multiplication(matrix[blockRow][blockColumn]);
            for row in [1 .. 2] do
                for column in [1 .. 2] do
                    result[2 * blockRow - 2 + row]
                          [2 * blockColumn - 2 + column] := small[row][column];
                od;
            od;
        od;
    od;
    return result;
end;;

# In Korhonen's B2 construction with q=2, mu=3 and nu=1, the underlying
# space is GF(4)^3 regarded over GF(2).  In the basis (1,omega) of each GF(4)
# coordinate, the quadratic form is the sum of the three norm maps.  Since
# N(a+b*omega)=a+b+a*b, the following formula evaluates that form without
# making any choice of a polynomial representation for GF(4).
Row2KorhonenQuadraticValue := function(vector)
    local value, position, first, second;
    if Length(vector) <> 6 then
        Error("Korhonen's quadratic form requires a binary vector of length six");
    fi;
    value := Row2Zero2;
    for position in [1, 3, 5] do
        first := vector[position];
        second := vector[position + 1];
        value := value + first + second + first * second;
    od;
    return value;
end;;

# Coordinates in R/Z(R) are taken with respect to the two specified
# generators of the extraspecial group R.  The central factor is found by
# an exhaustive calculation in the group of order 27, so no presentation or
# abstract group identification is used here.
Row2RadicalQuotientCoordinates := function(element, radicalBasis,
                                             centralGenerator)
    local first, second, centralPower;
    for first in [0 .. 2] do
        for second in [0 .. 2] do
            for centralPower in [0 .. 2] do
                if element = centralGenerator^centralPower
                             * radicalBasis[1]^first
                             * radicalBasis[2]^second then
                    return [first * One(GF(3)), second * One(GF(3))];
                fi;
            od;
        od;
    od;
    Error("an element of R has no coordinates in the specified basis");
end;;

Row2RadicalQuotientAction := function(element, radicalBasis,
                                       centralGenerator)
    return List(radicalBasis, generator ->
        Row2RadicalQuotientCoordinates(
            generator^element, radicalBasis, centralGenerator));
end;;

Row2CheckKorhonenAction := function(fullGroup, radical, radicalBasis,
                                    linearSubgroup, fieldAutomorphism)
    local centralGenerator, generators, actionMatrices, actionGroup,
          actionMap, alternatingForm, position, centralPower,
          linearActionMatrices, fieldAction;

    Row2Check("the specified generators generate the extraspecial 3-group",
              Group(radicalBasis), radical);
    centralGenerator := Comm(radicalBasis[1], radicalBasis[2]);
    Row2Check("the specified commutator generates the centre of the 3-group",
              Group([centralGenerator]), Centre(radical));
    Row2Check("normality of the extraspecial 3-group",
              IsNormal(fullGroup, radical), true);

    generators := GeneratorsOfGroup(fullGroup);
    actionMatrices := List(generators, element ->
        Row2RadicalQuotientAction(
            element, radicalBasis, centralGenerator));
    actionGroup := Group(actionMatrices);
    Row2Check("image on R/Z(R)", actionGroup, GL(2, 3));
    actionMap := GroupHomomorphismByImages(
                     fullGroup, GL(2, 3), generators, actionMatrices);
    Row2Check("conjugation homomorphism on R/Z(R)",
              actionMap = fail, false);
    Row2Check("the calculated map on R/Z(R) is a homomorphism",
              IsGroupHomomorphism(actionMap), true);
    Row2Check("image of the calculated map on R/Z(R)",
              Image(actionMap), GL(2, 3));
    Row2Check("kernel of the action on R/Z(R)",
              Kernel(actionMap), radical);

    alternatingForm := [[Zero(GF(3)), One(GF(3))],
                        [-One(GF(3)), Zero(GF(3))]];
    for position in [1 .. Length(generators)] do
        Row2Check("symplectic multiplier on R/Z(R)",
            actionMatrices[position] * alternatingForm
                * TransposedMat(actionMatrices[position]),
            DeterminantMat(actionMatrices[position]) * alternatingForm);
        centralPower := First([0 .. 2], power ->
            centralGenerator^generators[position]
                = centralGenerator^power);
        Row2Check("action on Z(R) agrees with the symplectic multiplier",
            centralPower * One(GF(3)),
            DeterminantMat(actionMatrices[position]));
    od;

    linearActionMatrices := List(GeneratorsOfGroup(linearSubgroup),
        element -> Row2RadicalQuotientAction(
            element, radicalBasis, centralGenerator));
    Row2Check("image of the GF(4)-linear normaliser on R/Z(R)",
              Group(linearActionMatrices), SL(2, 3));
    Row2Check("trivial multiplier of the GF(4)-linear normaliser",
              ForAll(linearActionMatrices,
                     matrix -> DeterminantMat(matrix) = One(GF(3))), true);

    fieldAction := Row2RadicalQuotientAction(
                       fieldAutomorphism, radicalBasis, centralGenerator);
    Row2Check("nontrivial multiplier of the GF(4) field automorphism",
              DeterminantMat(fieldAction), -One(GF(3)));
    Row2Check("the linear image and field automorphism generate GSp(2,3)",
        Group(Concatenation(linearActionMatrices, [fieldAction])),
        GL(2, 3));
    return actionMap;
end;;

Row2CheckOrder1296Matrices := function(matrices, radical, linearSubgroup,
                                      fieldAutomorphism, radicalBasis,
                                      basisMatrix)
    local fullGroup, centre, centralElement, radicalFactor, linearFactor,
          fullFactor, vectors, quadraticValue;
    fullGroup := matrices.group;
    Row2Check("order of Korhonen's group G_B2(3,1;GSp2(3))",
              Size(fullGroup), 1296);
    Row2Check("the recorded 3-core", PCore(fullGroup, 3), radical);
    Row2Check("order of the extraspecial 3-core", Size(radical), 27);
    Row2Check("exponent of the extraspecial 3-core", Exponent(radical), 3);
    centre := Centre(radical);
    Row2Check("centre of the extraspecial 3-core", Size(centre), 3);
    radicalFactor := FactorGroup(radical, centre);
    Row2Check("elementary abelian quotient of the extraspecial 3-core",
              IsElementaryAbelian(radicalFactor), true);
    Row2Check("order of the elementary abelian quotient",
              Size(radicalFactor), 9);

    Row2Check("order of the GF(4)-linear subgroup",
              Size(linearSubgroup), 648);
    Row2Check("the 3-core lies in the GF(4)-linear subgroup",
              IsSubgroup(linearSubgroup, radical), true);
    Row2Check("normal GF(4)-linear subgroup of index two",
              IsNormal(fullGroup, linearSubgroup), true);
    Row2Check("index of the GF(4)-linear subgroup",
              Index(fullGroup, linearSubgroup), 2);
    linearFactor := FactorGroup(linearSubgroup, radical);
    Row2Check("SL(2,3) quotient of the GF(4)-linear subgroup",
        IsomorphismGroups(linearFactor, SL(2, 3)) <> fail, true);

    fullFactor := FactorGroup(fullGroup, radical);
    Row2Check("order of the full quotient by the 3-core",
              Size(fullFactor), 48);
    Row2Check("GL(2,3) quotient of the full group",
        IsomorphismGroups(fullFactor, GL(2, 3)) <> fail, true);
    Row2Check("order of the GF(4) field automorphism",
              Order(fieldAutomorphism), 2);
    Row2Check("the field automorphism is outside the linear subgroup",
              fieldAutomorphism in linearSubgroup, false);
    centralElement := First(Elements(centre), element -> not IsOne(element));
    Row2Check("inversion of the extraspecial centre by the field automorphism",
              centralElement^fieldAutomorphism, centralElement^-1);

    # These checks identify the group with Korhonen's construction, rather
    # than merely with some extension having the same order and quotients.
    # The ordered basis of R/Z(R), its multiplier action, and the kernel of
    # that action are all calculated from the matrices themselves.
    Row2CheckKorhonenAction(fullGroup, radical, radicalBasis,
                            linearSubgroup, fieldAutomorphism);
    vectors := Tuples([Row2Zero2, Row2One2], 6);
    quadraticValue := vector ->
        Row2KorhonenQuadraticValue(vector * basisMatrix);
    Row2Check("number of zeros of Korhonen's B2 quadratic form",
        Number(vectors, vector -> IsZero(quadraticValue(vector))), 28);
    Row2Check("polarisation of Korhonen's B2 quadratic form",
        ForAll(vectors, first ->
            ForAll(vectors, second ->
                quadraticValue(first + second)
                    + quadraticValue(first) + quadraticValue(second)
                  = Row2BilinearValue(
                        first, Row2CanonicalAlternatingForm(6), second))),
        true);
    Row2Check("Korhonen's B2 quadratic form is fixed by the group",
        ForAll(GeneratorsOfGroup(fullGroup), generator ->
            ForAll(vectors, vector ->
                quadraticValue(vector * generator)
                    = quadraticValue(vector))), true);
    Row2Check("the group preserves a quadratic form of minus type",
              "minus" in Row2InvariantQuadraticTypes(fullGroup), true);
    matrices.radical := radical;
    matrices.linearSubgroup := linearSubgroup;
    matrices.fieldAutomorphism := fieldAutomorphism;
    return matrices;
end;;

Row2Order1296Matrices := function()
    local field, one, omega, shift, diagonal, fourier, shear, radical,
          ambient, linearNormaliser, korhonenLinearNormaliser,
          korhonenSemilinearGroup, binaryRadicalGenerators,
          binaryLinearGenerators, frobenius, rawGenerators,
          invariantForm, basisMatrix, changedRadical, changedLinear,
          changedFrobenius, changedRadicalBasis, fixedRadicalGenerators,
          fixedLinearGenerators, fixedFrobenius, fixed;

    field := GF(4);
    one := One(field);
    omega := Z(4);
    shift := NullMat(3, 3, field);
    shift[1][2] := one;
    shift[2][3] := one;
    shift[3][1] := one;
    diagonal := DiagonalMat([one, omega, omega^2]);
    radical := Group([shift, diagonal]);
    Row2Check("order of the extraspecial group over GF(4)",
              Size(radical), 27);
    Row2Check("central scalar subgroup F0 in Korhonen's construction",
        Centre(radical), Group([omega * IdentityMat(3, field)]));

    # These are the matrices A, B, C and E from Korhonen's construction of
    # the absolutely irreducible representation of 3_+^(1+2).  The scalar
    # group of GL(3,4) is already Z(R), so these four matrices generate the
    # full GF(4)-linear normaliser prescribed there.
    fourier := List([0 .. 2], row ->
        List([0 .. 2], column -> omega^(row * column)));
    shear := DiagonalMat([one, one, omega]);
    korhonenLinearNormaliser := Group(
        [diagonal, shift, fourier, shear]);
    ambient := GL(3, 4);
    linearNormaliser := Normalizer(ambient, radical);
    Row2Check("order of the GF(4)-linear normaliser",
              Size(linearNormaliser), 648);
    Row2Check("Korhonen's generators give the GF(4)-linear normaliser",
              korhonenLinearNormaliser, linearNormaliser);
    binaryRadicalGenerators := List([diagonal, shift],
        matrix -> Row2RestrictionFromGF4(matrix, omega));
    binaryLinearGenerators := List(GeneratorsOfGroup(linearNormaliser),
        matrix -> Row2RestrictionFromGF4(matrix, omega));
    frobenius := Row2BlockDiagonalMatrix(List([1 .. 3], position ->
        Row2BinaryMatrix([[1, 0], [1, 1]])));
    rawGenerators := Concatenation(binaryLinearGenerators, [frobenius]);
    korhonenSemilinearGroup := Group(Concatenation(
        List([diagonal, shift, fourier, shear],
             matrix -> Row2RestrictionFromGF4(matrix, omega)),
        [frobenius]));
    Row2Check("specialisation of Korhonen's B2 construction",
              Group(rawGenerators), korhonenSemilinearGroup);
    invariantForm := Row2InvariantAlternatingForm(rawGenerators, 6);

    # The recorded basis change is an explicit witness that the fixed binary
    # matrices are the restriction-of-scalars construction above.  Thus the
    # verification does not identify the group merely from its order and
    # abstract quotient structure.
    if not IsBound(Row2RecordedOrder1296Data)
       or not IsRecord(Row2RecordedOrder1296Data)
       or not IsBound(Row2RecordedOrder1296Data.radical)
       or Length(Row2RecordedOrder1296Data.radical) = 0
       or not IsBound(Row2RecordedOrder1296Data.linearNormaliser)
       or Length(Row2RecordedOrder1296Data.linearNormaliser) = 0
       or not IsBound(Row2RecordedOrder1296Data.fieldAutomorphism)
       or Length(Row2RecordedOrder1296Data.fieldAutomorphism) = 0
       or not IsBound(Row2RecordedOrder1296Data.basisChange)
       or Length(Row2RecordedOrder1296Data.basisChange) = 0 then
        Error("all four recorded data sets for the group of order 1296 ",
              "are required");
    fi;
    basisMatrix := Row2BinaryMatrixFromRows(
                       Row2RecordedOrder1296Data.basisChange);
    Row2Check("rank of the recorded basis change for the group of order 1296",
              RankMat(basisMatrix), 6);
    Row2Check("recorded basis change for the group of order 1296",
        basisMatrix * invariantForm * TransposedMat(basisMatrix),
        Row2CanonicalAlternatingForm(6));
    changedRadical := Group(List(binaryRadicalGenerators, generator ->
        basisMatrix * generator * basisMatrix^-1));
    changedRadicalBasis := List(binaryRadicalGenerators, generator ->
        basisMatrix * generator * basisMatrix^-1);
    changedLinear := Group(List(binaryLinearGenerators, generator ->
        basisMatrix * generator * basisMatrix^-1));
    changedFrobenius := basisMatrix * frobenius * basisMatrix^-1;

    fixedLinearGenerators := List(
        Row2RecordedOrder1296Data.linearNormaliser,
        Row2BinaryMatrixFromRows);
    fixedRadicalGenerators := List(
        Row2RecordedOrder1296Data.radical,
        Row2BinaryMatrixFromRows);
    fixedFrobenius := Row2BinaryMatrixFromRows(
                          Row2RecordedOrder1296Data.fieldAutomorphism);
    fixed := rec(
        dimension := 6,
        generators := Concatenation(fixedLinearGenerators,
                                     [fixedFrobenius]),
        group := Group(Concatenation(fixedLinearGenerators,
                                     [fixedFrobenius])));
    Row2Check("fixed extraspecial group from the GF(4) construction",
              Group(fixedRadicalGenerators), changedRadical);
    Row2Check("fixed ordered basis of the extraspecial quotient",
              fixedRadicalGenerators, changedRadicalBasis);
    Row2Check("fixed linear normaliser from the GF(4) construction",
              Group(fixedLinearGenerators), changedLinear);
    Row2Check("fixed field automorphism from the GF(4) construction",
              fixedFrobenius, changedFrobenius);
    Row2Check("fixed group from the GF(4) construction",
              fixed.group,
              Group(Concatenation(GeneratorsOfGroup(changedLinear),
                                  [changedFrobenius])));
    Row2Check("fixed alternating form for the recorded group of order 1296",
        ForAll(fixed.generators, generator ->
            generator * Row2CanonicalAlternatingForm(6)
                * TransposedMat(generator)
              = Row2CanonicalAlternatingForm(6)), true);
    return Row2CheckOrder1296Matrices(
        fixed, Group(fixedRadicalGenerators),
        Group(fixedLinearGenerators), fixedFrobenius,
        fixedRadicalGenerators, basisMatrix);
end;;

Row2ConstructCover := function()
    local a2, b2, c2, c4plus, c6wreath, c8wreath, a3, f3,
          b1threeRaw, b1three, a4, f4, r5, c4minus, gamma16,
          b1fourRaw, b1four, a8, f8, cyclic17, group1296,
          c4minusWreath, c6second, pairC4plus, pairGamma16,
          cover;

    Row2Check("the fixed symplectic basis of the quotient",
              Row2CommutatorForm, Row2CanonicalAlternatingForm(8));
    a2 := Row2BinaryMatrix([[0, 1], [1, 1]]);
    b2 := Row2BinaryMatrix([[0, 1], [1, 0]]);
    c2 := rec(dimension := 2, generators := [a2, b2],
              group := Group([a2, b2]));
    Row2Check("order of the standard element of order three in S3",
              Order(a2), 3);
    Row2Check("order of the standard involution in S3", Order(b2), 2);
    Row2Check("inversion in the standard copy of S3",
              b2 * a2 * b2^-1, a2^-1);
    Row2Check("order of Sp(2,2)", Size(c2.group), 6);
    c4plus := Row2WreathProductMatrices(c2, 2);
    Row2Check("order of O+(4,2)", Size(c4plus.group), 72);
    Row2Check("plus type of O+(4,2)",
              "plus" in Row2InvariantQuadraticTypes(c4plus.group), true);
    c6wreath := Row2WreathProductMatrices(c2, 3);
    Row2Check("minus type of S3 wr S3",
              "minus" in Row2InvariantQuadraticTypes(c6wreath.group), true);
    c8wreath := Row2WreathProductMatrices(c2, 4);

    # The next two B1 groups are the field models in Korhonen,
    # Remark 2.9.10.  The two diagonal blocks are the mutually dual
    # GF(2)-modules, and the third generator interchanges them.
    a3 := Row2BinaryMatrix([
        [0, 1, 0], [0, 0, 1], [1, 1, 0]]);
    f3 := Row2BinaryMatrix([
        [1, 0, 0], [0, 0, 1], [0, 1, 1]]);
    Row2Check("order of multiplication on GF(8)", Order(a3), 7);
    Row2Check("order of Frobenius on GF(8)", Order(f3), 3);
    Row2Check("Frobenius relation on GF(8)",
              f3^-1 * a3 * f3, a3^2);
    b1threeRaw := [
        Row2BlockDiagonalMatrix([a3, a3^-1]),
        Row2BlockDiagonalMatrix([f3, f3]),
        Row2BlockInterchange(3, 2, 1, 2)
    ];
    b1three := Row2CanonicalSymplecticGroup(b1threeRaw);
    Row2Check("inversion in the group 7:6",
        b1threeRaw[3] * b1threeRaw[1] * b1threeRaw[3]^-1,
        b1threeRaw[1]^-1);
    Row2Check("the involution centralises Frobenius in 7:6",
        b1threeRaw[3] * b1threeRaw[2] * b1threeRaw[3]^-1,
        b1threeRaw[2]);
    Row2Check("order of 7:6", Size(b1three.group), 42);
    Row2Check("plus type of 7:6",
              "plus" in Row2InvariantQuadraticTypes(b1three.group), true);
    Row2Check("paired subgroup 7:3",
        Size(Group(b1three.generators{[1, 2]})), 21);

    a4 := Row2BinaryMatrix([
        [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0]]);
    f4 := Row2BinaryMatrix([
        [1, 0, 0, 0], [0, 0, 1, 0], [1, 1, 0, 0], [0, 0, 1, 1]]);
    Row2Check("order of multiplication on GF(16)", Order(a4), 15);
    Row2Check("order of Frobenius on GF(16)", Order(f4), 4);
    Row2Check("Frobenius relation on GF(16)",
              f4^-1 * a4 * f4, a4^2);
    # The subgroup generated by a4^3 and f4 is the B2 field model in
    # Korhonen, Remark 2.9.11, with m=2.
    r5 := a4^3;
    Row2Check("order of the element in 5:4", Order(r5), 5);
    c4minus := Row2CanonicalSymplecticGroup([r5, f4]);
    Row2Check("order of 5:4", Size(c4minus.group), 20);
    Row2Check("minus type of 5:4",
              "minus" in Row2InvariantQuadraticTypes(c4minus.group), true);
    gamma16 := rec(dimension := 4, generators := [a4, f4],
                   group := Group([a4, f4]));
    Row2Check("order of GammaL(1,16)", Size(gamma16.group), 60);
    b1fourRaw := [
        Row2BlockDiagonalMatrix([a4, a4^-1]),
        Row2BlockDiagonalMatrix([f4, f4]),
        Row2BlockInterchange(4, 2, 1, 2)
    ];
    b1four := Row2CanonicalSymplecticGroup(b1fourRaw);
    Row2Check("inversion in the B1 group of dimension eight",
        b1fourRaw[3] * b1fourRaw[1] * b1fourRaw[3]^-1,
        b1fourRaw[1]^-1);
    Row2Check("the involution centralises Frobenius in the B1 group",
        b1fourRaw[3] * b1fourRaw[2] * b1fourRaw[3]^-1,
        b1fourRaw[2]);
    Row2Check("order of the B1 group in dimension eight",
              Size(b1four.group), 120);
    Row2Check("plus type of the B1 group in dimension eight",
              "plus" in Row2InvariantQuadraticTypes(b1four.group), true);
    Row2Check("paired subgroup GammaL(1,16)",
        Size(Group(b1four.generators{[1, 2]})), 60);

    # The matrices a8^15 and f8 give the same B2 field model with m=4.
    a8 := Row2BinaryMatrix([
        [0,1,0,0,0,0,0,0], [0,0,1,0,0,0,0,0],
        [0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0],
        [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0],
        [0,0,0,0,0,0,0,1], [1,0,1,1,1,0,0,0]
    ]);
    f8 := Row2BinaryMatrix([
        [1,0,0,0,0,0,0,0], [0,0,1,0,0,0,0,0],
        [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
        [1,0,1,1,1,0,0,0], [0,0,1,0,1,1,1,0],
        [1,0,1,1,0,0,1,1], [1,1,0,0,1,0,0,0]
    ]);
    Row2Check("order of multiplication on GF(256)", Order(a8), 255);
    Row2Check("order of Frobenius on GF(256)", Order(f8), 8);
    Row2Check("Frobenius relation on GF(256)",
              f8^-1 * a8 * f8, a8^2);
    cyclic17 := Row2CanonicalSymplecticGroup([a8^15, f8]);
    Row2Check("order of 17:8", Size(cyclic17.group), 136);
    Row2Check("minus type of 17:8",
              "minus" in Row2InvariantQuadraticTypes(cyclic17.group), true);

    group1296 := Row2Order1296Matrices();
    c4minusWreath := Row2WreathProductMatrices(c4minus, 2);
    c6second := Row2DirectProductMatrices([c4minus, c2]);
    pairC4plus := Row2PairedMatrices(c4plus);
    pairGamma16 := Row2PairedMatrices(gamma16);

    cover := [
        Row2CoverEntry("S3 wr S4", "O8 plus, four blocks",
            c8wreath, 31104, "plus"),
        Row2CoverEntry("(5:4) wr S2", "O8 plus, two blocks",
            c4minusWreath, 800, "plus"),
        Row2CoverEntry("B1(1,4)", "O8 plus, field pair",
            b1four, 120, "plus"),
        Row2CoverEntry("G_B2(3,1;GSp2(3)) x S3",
            "O8 plus, dimensions six and two",
            Row2DirectProductMatrices([group1296, c2]), 7776, "plus"),
        Row2CoverEntry("17:8", "O8 minus, cyclic semilinear",
            cyclic17, 136, "minus"),
        Row2CoverEntry("(5:4) x (S3 wr S2)",
            "O8 minus, dimensions four and four",
            Row2DirectProductMatrices([c4minus, c4plus]), 1440, "minus"),
        Row2CoverEntry("(7:6) x S3",
            "O8 minus, dimensions six and two",
            Row2DirectProductMatrices([b1three, c2]), 252, "minus"),
        Row2CoverEntry("pair(S3 wr S2)", "paired four-spaces",
            pairC4plus, 72, "plus"),
        Row2CoverEntry("pair(GammaL(1,16))", "paired four-spaces",
            pairGamma16, 60, "plus"),
        Row2CoverEntry("(S3 wr S2) x (S3 wr S2)",
            "nondegenerate four plus four",
            Row2DirectProductMatrices([c4plus, c4plus]), 5184, "plus"),
        Row2CoverEntry("(S3 wr S2) x (5:4)",
            "nondegenerate four plus four",
            Row2DirectProductMatrices([c4plus, c4minus]), 1440, "minus"),
        Row2CoverEntry("(5:4) x (5:4)",
            "nondegenerate four plus four",
            Row2DirectProductMatrices([c4minus, c4minus]), 400, "plus"),
        Row2CoverEntry("S3 x (7:6)",
            "nondegenerate two plus six",
            Row2DirectProductMatrices([c2, b1three]), 252, "minus"),
        Row2CoverEntry("S3 x ((5:4) x S3)",
            "nondegenerate two plus six",
            Row2DirectProductMatrices([c2, c6second]), 720, "minus"),
        Row2CoverEntry("S3 x (S3 wr S3)",
            "nondegenerate two plus six",
            Row2DirectProductMatrices([c2, c6wreath]), 7776, "plus"),
        Row2CoverEntry("S3 x G_B2(3,1;GSp2(3))",
            "nondegenerate two plus six",
            Row2DirectProductMatrices([c2, group1296]), 7776, "plus")
    ];
    Row2Check("number of groups in the row-2 cover", Length(cover), 16);
    Row2Check("sum of the orders in the row-2 cover",
              Sum(List(cover, entry -> entry.order)), 65308);
    return cover;
end;;
