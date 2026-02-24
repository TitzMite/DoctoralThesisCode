
The GAP code provided in this folder can verify the following results:

(1) The links of the complexes Delta1, ..., Delta13 are all generalized triangles.
In particular, the universal covers are A2-tilde-buildings. Note that this could be
easily checked by hand.

(2) Every type-preserving, vertex-regular lattice arises from one of the GABs we
provide.

(3) The cellular automorphism groups of the GABs are as indicated in the thesis.

(4) The GABs admit the extensions indicated in Table 4.1.

(5) The fundamental groups of the GABs admit the quotients as described in the thesis.

(6) We verify the claims made in Proposition 88.

(7) The 2-balls in the buildings X1, ..., X13 are as indicated in Table 4.3.

(8) The numbers given in Table B.4 are correct.

(9) The 4-balls in the building X6 are the 4-balls in the building associated to PGL(3,Q2).


-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------

Throughout the code we use a structure that we call RaduDatumWithCover. This is a pair where
the first entry is a triple consisting of three ordered point line geometries and the second 
entry is a triangle cover. The first entry corresponds to a Radu graph and the second entry
to a perfect cover. In particular, a RaduDatumWithCover encodes the same information as a
triangle complex. With the functions TripleTrianglesRaduDatumWithCover(...) and
RaduDatumWithCoverFromTriangles(...) we can interchange between triangle complexes and
RaduDatumWithCover. 

-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------

The file "11_verification.g" contains the function VerifyClaims(), which verifies all claims, except
for (8), in less than an hour. For (8), one can use the function Compute4BallData(...) in
"10_building_autos.g" but each computation will take several days.

The function "00_main.g" reads in all files needed to execute the verification functions.