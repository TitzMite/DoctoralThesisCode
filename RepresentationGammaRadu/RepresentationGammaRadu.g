
LoadPackage("KBMAG");

F := FreeGroup("a","b","c","x","y","z");
AssignGeneratorVariables(F);

RelsRadu :=
    [
        a^2, b^2, c^2, x^2, y^2, z^2,
        a * x * a * x,
        a * y * a * y,
        a * z * b * z,
        b * x * b * x,
        b * y * c * y,
        c * x * c * z
    ];

Radu33 := F/RelsRadu;

pro := GroupHomomorphismByImages(F,Radu33);

pi1S := Group([(a*b)^pro, (y*x)^pro]);
t := Indeterminate(Rationals, "t");
poly := t^8 + 106*t^6 + 2825*t^4 + 1868*t^2 + 64;
K := AlgebraicExtension(Rationals, poly, "zeta");
one := One(K);
zero := Zero(K);
zeta := RootOfDefiningPolynomial(K);

u := Indeterminate(K, "u");

pol_alpha := u^2-u-4;
alpha := RootsOfPolynomial(pol_alpha)[1];

pol_beta := u^2-u+4;
beta := RootsOfPolynomial(pol_beta)[1];

pol_gamma := u^2-alpha+12;
gamma := RootsOfPolynomial(pol_gamma)[1];

AB := 1/4*[[-alpha+gamma, zero], [zero, -alpha -gamma]];

YX :=
    [
        [one, -1 + alpha/2 + beta/4 - 3/16*alpha*beta + 1/2*beta*gamma + 1/16*beta*gamma^3],
        [-1 + alpha/2 + beta/4-3/16*alpha*beta - 1/2*beta*gamma - 1/16*beta*gamma^3 , one]
    ];

Lin := Group([AB,YX]);

#since hom is not fail the homomorphism is well defined
hom := GroupHomomorphismByImages(pi1S, Lin);

rws := KBMAGRewritingSystem(Radu33);
KnuthBendix(rws);

short_elements_in_finite_residual := function()
    local words;
    words := EnumerateReducedWords(rws, 1, 8);
    words := Filtered(words, w->w^pro in pi1S);
    return Filtered(words, w-> (w^pro)^hom = One(Lin)); 
end;

