# Common projective action for the extraspecial groups on GF(3)^16.

GF316ProjectiveRegularCoreAction := function(coreMatrices,
    quotientMatrices, liftMatrices)
    local F, zero, one, lineCount, offsets, enumerators, lineNumber,
          lineVector, zeroByteString, setThreeByteNumber,
          getThreeByteNumber, E, seen, orbitNumbers,
          regularCoreRepresentatives, position, v, orbit, lineNumbers, number,
          regularCoreNumber, projectiveOrbitCount, regularCorePermutations,
          lift, images,
          quotient, quotientImage, hom, i;

    F := GF(3);;
    zero := Zero(F);;
    one := One(F);;
    lineCount := (3^16 - 1) / 2;;
    offsets := List([1 .. 16], i ->
        Sum([1 .. i - 1], j -> 3^(16 - j)));;
    enumerators := List([0 .. 15], d -> EnumeratorSorted(F^d));;

    lineNumber := function(w)
        local first, factor, tail;
        first := PositionProperty(w, x -> not IsZero(x));;
        if first = fail then
            Error("the zero vector does not define a projective point");
        fi;
        factor := w[first]^-1;;
        if first = 16 then
            return offsets[first] + 1;
        fi;
        tail := List(w{[first + 1 .. 16]}, x -> factor * x);;
        return offsets[first] + NumberFFVector(tail, 3) + 1;
    end;;

    lineVector := function(index)
        local remainder, dimension, block, first, tail;
        if index < 1 or index > lineCount then
            Error("projective-point number outside its range");
        fi;
        remainder := index - 1;;
        for first in [1 .. 16] do
            dimension := 16 - first;;
            block := 3^dimension;;
            if remainder < block then
                tail := enumerators[dimension + 1][remainder + 1];;
                return Concatenation(
                    ListWithIdenticalEntries(first - 1, zero),
                    [ one ], tail);
            fi;
            remainder := remainder - block;;
        od;
        Error("could not decode a projective-point number");
    end;;

    zeroByteString := function(length)
        local result, blockLength, block, remaining;
        result := EmptyString(length);;
        blockLength := Minimum(length, 1048576);;
        block := ListWithIdenticalEntries(blockLength, CHAR_INT(0));;
        ConvertToStringRep(block);;
        while Length(result) + blockLength <= length do
            Append(result, block);
        od;
        remaining := length - Length(result);;
        if remaining > 0 then
            Append(result, block{[1 .. remaining]});
        fi;
        return result;
    end;;

    setThreeByteNumber := function(bytes, index, value)
        bytes[1][index] := CHAR_INT(value mod 256);;
        value := QuoInt(value, 256);;
        bytes[2][index] := CHAR_INT(value mod 256);;
        bytes[3][index] := CHAR_INT(QuoInt(value, 256) mod 256);;
    end;;

    getThreeByteNumber := function(bytes, index)
        return INT_CHAR(bytes[1][index])
            + 256 * INT_CHAR(bytes[2][index])
            + 65536 * INT_CHAR(bytes[3][index]);
    end;;

    Assert(0, Length(quotientMatrices) = Length(liftMatrices));;
    Assert(0, ForAll([1, 2, 3, 17, 1000, lineCount], i ->
        lineNumber(lineVector(i)) = i));;
    E := Group(coreMatrices);;
    Assert(0, Size(E) = 512);;

    seen := BlistList([1 .. lineCount], []);;
    orbitNumbers := [ zeroByteString(lineCount), zeroByteString(lineCount),
        zeroByteString(lineCount) ];;
    regularCoreRepresentatives := [];;
    projectiveOrbitCount := 0;;
    position := Position(seen, false);;
    while position <> fail do
        v := lineVector(position);;
        orbit := Orbit(E, v, OnLines);;
        lineNumbers := List(orbit, lineNumber);;
        Assert(0, Length(lineNumbers) = Length(Set(lineNumbers)));;
        for number in lineNumbers do
            seen[number] := true;
        od;
        if Length(orbit) = 256 then
            Add(regularCoreRepresentatives, v);;
            regularCoreNumber := Length(regularCoreRepresentatives);;
            for number in lineNumbers do
                setThreeByteNumber(orbitNumbers, number, regularCoreNumber);
            od;
        fi;
        projectiveOrbitCount := projectiveOrbitCount + 1;;
        Unbind(orbit);;
        position := Position(seen, false, position);;
    od;
    Assert(0, Number(seen, x -> x) = lineCount);;
    Assert(0, Length(regularCoreRepresentatives) < 2^24);;

    regularCorePermutations := [];;
    for lift in liftMatrices do
        images := List(regularCoreRepresentatives, v ->
            getThreeByteNumber(orbitNumbers, lineNumber(v * lift)));;
        Assert(0, not 0 in images);;
        Assert(0, Set(images) = [1 .. Length(regularCoreRepresentatives)]);;
        Add(regularCorePermutations, PermList(images));;
    od;
    quotient := Group(quotientMatrices);;
    quotientImage := Group(regularCorePermutations);;
    hom := GroupHomomorphismByImages(quotient, quotientImage,
        quotientMatrices, regularCorePermutations);;
    Assert(0, hom <> fail and Image(hom) = quotientImage);;
    Assert(0, ForAll([1 .. Length(quotientMatrices)], i ->
        Image(hom, quotientMatrices[i]) = regularCorePermutations[i]));;

    Unbind(seen);;
    Unbind(orbitNumbers);;
    CollectGarbage(true);;
    return rec(
        lineCount := lineCount,
        projectiveOrbitCount := projectiveOrbitCount,
        regularCoreOrbitCount := Length(regularCoreRepresentatives),
        regularCoreRepresentatives := regularCoreRepresentatives,
        quotientImage := quotientImage,
        quotientHomomorphism := hom);
end;;
