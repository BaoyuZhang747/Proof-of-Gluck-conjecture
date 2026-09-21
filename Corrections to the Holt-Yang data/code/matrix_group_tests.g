
# Procedures for deciding whether a subgroup G of GL(d,p) satisfies the five
# nonautomatic conditions used below: solvability, irreducibility,
# quasiprimitivity, nonmetacyclicity and the absence of a regular orbit.
# Faithfulness is automatic because G is given as a matrix subgroup.

# A group G <= GL(d,p) qualifies exactly when all five conditions hold:

#    (i)   G is solvable;
#    (ii)  G acts irreducibly on V = GF(p)^d;
#    (iii) G is quasiprimitive, i.e. every normal subgroup of G acts
#          homogeneously on V;
#    (iv)  G is not metacyclic;
#    (v)   G has no regular orbit on V, i.e. every vector has a non-trivial
#          stabiliser.

# The procedures use the GAP library, IrredSol and the MeatAxe functions.

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

# Homogeneity of the action of a subgroup.

# A GF(p)[N]-module is homogeneous iff it is a direct sum of isomorphic
# irreducible modules.  MTX.HomogeneousComponents groups isomorphic
# indecomposable summands, so one component is not enough: that component
# must itself be irreducible.  The trivial subgroup and scalar subgroups act
# homogeneously by definition.

ActsHomogeneously := function(N, p, d)
    local M, hc;
    if Size(N) = 1 then
        return true;
    fi;
    if Length(GeneratorsOfGroup(N)) = 0 then
        return true;
    fi;
    M := GModuleByMats(GeneratorsOfGroup(N), GF(p));
    if MTX.Dimension(M) <> d then
        return false;
    fi;
    hc := MTX.HomogeneousComponents(M);
    return Length(hc) = 1
       and MTX.IsIrreducible(hc[1].component[2]);
end;;

# Quasiprimitivity.

# G is quasiprimitive iff every normal subgroup acts homogeneously.  For a
# solvable matrix group of moderate order the direct computation of the
# normal subgroup lattice in the matrix representation is expensive, so we
# transport the group to an isomorphic polycyclic (pc) group, list the normal subgroups
# there, and pull each one back to a matrix subgroup for the homogeneity test.

IsQuasiprimitiveLinearGroup := function(G, p, d)
    local iso, P, normalsP, N, gensP, gensMat, x;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    normalsP := NormalSubgroups(P);
    for N in normalsP do
        gensP := GeneratorsOfGroup(N);
        gensMat := List(gensP, x -> PreImagesRepresentative(iso, x));
        if not ActsHomogeneously(Subgroup(G, gensMat), p, d) then
            return false;
        fi;
    od;
    return true;
end;;

# Metacyclicity.

# A group is metacyclic iff it has a cyclic normal subgroup with cyclic
# quotient.  We again work in a pc-group, where this is inexpensive.

IsMetacyclicSolvableGroup := function(G)
    local iso, P, N;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    if IsCyclic(P) then
        return true;
    fi;
    for N in NormalSubgroups(P) do
        if IsCyclic(N) and IsCyclic(FactorGroup(P, N)) then
            return true;
        fi;
    od;
    return false;
end;;

# When an enumeration requires both tests, the normal subgroups of the pc
# image are formed only once.
IsQuasiprimitiveNonmetacyclicLinearGroup := function(G, p, d)
    local iso, P, normalsP, N, gensMat, x;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    normalsP := NormalSubgroups(P);
    for N in normalsP do
        gensMat := List(GeneratorsOfGroup(N),
                        x -> PreImagesRepresentative(iso, x));
        if not ActsHomogeneously(Subgroup(G, gensMat), p, d) then
            return false;
        fi;
    od;
    if IsCyclic(P) then
        return false;
    fi;
    for N in normalsP do
        if IsCyclic(N) and IsCyclic(FactorGroup(P, N)) then
            return false;
        fi;
    od;
    return true;
end;;

# Absence of a regular orbit.

# We walk over all nonzero vectors, growing the orbit of each previously
# unseen vector.  A regular orbit exists exactly when one orbit has size |G|.

# The list of all vectors of a space depends only on p and d, and the test is
# applied to many groups on the same space, so each list is formed once and
# retained for the remaining calculations.
AllVectorLists := rec();;

HasRegularOrbitBySweep := function(G, p, d)
    local V, key, allVecs, zero, order, gens, seen, index, startVector, idx, queue,
          head, size, v, g, w;
    order := Size(G);
    V := GF(p)^d;
    if order > p^d - 1 then
        return false;           # an orbit can never reach size |G|
    fi;
    key := Concatenation(String(p), "_", String(d));
    if not IsBound(AllVectorLists.(key)) then
        AllVectorLists.(key) := AsList(V);
    fi;
    allVecs := AllVectorLists.(key);
    zero := Zero(V);
    gens := GeneratorsOfGroup(G);
    index := v -> NumberFFVector(v, p) + 1;
    seen := BlistList([1 .. p^d], []);
    seen[index(zero)] := true;
    for startVector in allVecs do
        idx := index(startVector);
        if not seen[idx] then
            queue := [startVector];
            seen[idx] := true;
            head := 1;
            size := 0;
            while head <= Length(queue) do
                v := queue[head];
                head := head + 1;
                size := size + 1;
                for g in gens do
                    w := v * g;
                    idx := index(w);
                    if not seen[idx] then
                        seen[idx] := true;
                        Add(queue, w);
                    fi;
                od;
            od;
            if size = order then
                return true;
            fi;
        fi;
    od;
    return false;
end;;

HasNoRegularOrbit := function(G, p, d)
    return not HasRegularOrbitBySweep(G, p, d);
end;;

# The five Holt--Yang criteria together.

# The five criteria are a conjunction, so they may be tested in any order.  The
# absence of a regular orbit is both the most selective of them and the one
# that needs no pc image, so it is tested first: on GF(5)^8 it leaves 114 of
# the 1301 candidates, and only those are carried to the quasiprimitivity
# test, which is the substantial part of this calculation.
SatisfiesHoltYangCriteria := function(G, p, d)
    if not HasNoRegularOrbit(G, p, d) then return false; fi;
    if not IsSolvableGroup(G) then return false; fi;
    if not MTX.IsIrreducible(GModuleByMats(GeneratorsOfGroup(G), GF(p))) then
        return false;
    fi;
    return IsQuasiprimitiveNonmetacyclicLinearGroup(G, p, d);
end;;

# A characteristic-polynomial conjugacy invariant.

# Conjugate subgroups afford the same representation, so they have the same
# multiset of characteristic polynomials of elements.  We record this multiset
# through the conjugacy classes of G (computed in an isomorphic pc group):
# for each class we store its size together with the coefficient list of the
# characteristic polynomial of a representative.  Two subgroups with different
# invariants are certainly not GL(d,p)-conjugate; equality identifies
# candidates for an exact conjugacy test, which is carried out with
# AreConjugateInGL below.

CharacteristicPolynomialConjugacyInvariant := function(G)
    local iso, P, classes;
    iso := IsomorphismPcGroup(G);
    P := Image(iso);
    classes := ConjugacyClasses(P);
    return [ Size(G),
             SortedList(List(classes, c ->
                 [ Size(c),
                   CoefficientsOfUnivariatePolynomial(
                       CharacteristicPolynomial(
                           PreImagesRepresentative(iso, Representative(c)))) ])) ];
end;;

# Exact GL(d,p)-conjugacy of two irreducible subgroups.

# Two irreducible subgroups G, H <= GL(d,p) are conjugate in GL(d,p) iff there
# is a group isomorphism phi: G -> H that is realised by a change of basis,
# i.e. such that the natural G-module and the phi-pullback of the H-module are
# isomorphic.  Every isomorphism differs from a fixed one by an automorphism of
# G, and inner automorphisms do not change the GL-conjugacy class; so it is
# enough to test one isomorphism per coset of Inn(G) in Aut(G), i.e. one
# representative for each element of Out(G).  The MeatAxe matrix is substituted in each
# matched generator equation, and the conjugated group is compared with H.

AreConjugateInGL := function(G, H, p)
    local isoG, PG, isoH, PH, phi, A, inner, transversal, gens, sourceMats,
          Mg, alpha, imgs, Mh, x, i, conjugated;
    if Size(G) <> Size(H) then
        return false;
    fi;
    isoG := IsomorphismPcGroup(G);  PG := Image(isoG);
    isoH := IsomorphismPcGroup(H);  PH := Image(isoH);
    phi := IsomorphismGroups(PG, PH);
    if phi = fail then
        return false;               # not even abstractly isomorphic
    fi;
    A := AutomorphismGroup(PG);
    inner := InnerAutomorphismsAutomorphismGroup(A);
    transversal := List(RightCosets(A, inner), Representative);
    gens := GeneratorsOfGroup(PG);
    sourceMats := List(gens, g -> PreImagesRepresentative(isoG, g));
    Mg := GModuleByMats(sourceMats, GF(p));
    for alpha in transversal do
        imgs := List(gens, x ->
            PreImagesRepresentative(isoH, Image(phi, Image(alpha, x))));
        Mh := GModuleByMats(imgs, GF(p));
        x := MTX.IsomorphismModules(Mg, Mh);
        if x <> fail and RankMat(x) = Length(x) then
            if ForAll([1 .. Length(sourceMats)],
                      i -> x^-1 * sourceMats[i] * x = imgs[i]) then
                conjugated := Group(List(sourceMats, g -> x^-1 * g * x));
                if conjugated = H then return true; fi;
            fi;
        fi;
    od;
    return false;
end;;
