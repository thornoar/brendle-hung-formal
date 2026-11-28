import smoothmanifold;

defaultpen(fontsize(11pt));
size(10cm);

config.smooth.nodesize = 0.8;

usepackage("amssymb");
usepackage("amsmath");

smooth trm1 = node("$5$", (-3,0));
smooth trm2 = node("$(x \mapsto x^2)$", (-1.3,-1.5));
smooth trm25 = node("$(z \mapsto z^3)$", (.2,0.2));
smooth trm3 = node("$\pi$", (2.5,1.1));
smooth trm4 = node("$D_{20}$", (4.9,-.4));
smooth trm5 = node("$(\mathbb{S}^2, 3)$", (8,0));

smooth typ1 = node("$\mathrm{Nat}$", (-3,-4));
smooth typ2 = node("$\mathrm{Real} \to \mathrm{Real}$", (-.4,-5));
smooth typ3 = node("$\mathrm{Real}$", (2.5,-3.5));
smooth typ4 = node("$\mathrm{Group}$", (4.9,-4.4));
smooth typ5 = node("$\mathrm{Top} \times \mathrm{Nat}$", (8,-4));

smooth sort1 = node("$U_1$", (2.5, -8));
smooth sort2 = node("$\mathrm{Nat} \times U_1$", (-2.5, -8.2));
smooth sort3 = node("$U_1 \to \mathrm{Group}$", (7.2, -8.5));

smooth ssort1 = node("$U_2$", (2.5, -11));
// smooth ssort2 = node("$\mathrm{Nat} \times U_1$", (-2.5, -8.2));
// smooth ssort3 = node("$U_1 \to \mathrm{Group}$", (7.2, -8.5));

smooth so_on = node("$\vdots$", (2.5, -13), size = 0.15);

draw(smooth.cache, dspec = nodepar());

drawarrow(trm1, typ1);
drawarrow(trm2, typ2, curve = 0.05);
drawarrow(trm25, typ2, curve = -0.05);
drawarrow(trm3, typ3);
drawarrow(trm4, typ4);
drawarrow(trm5, typ5);

drawarrow(typ1, sort1, curve = 0.15);
drawarrow(typ2, sort1);
drawarrow(typ3, sort1);
drawarrow(typ4, sort1);
drawarrow(typ5, sort1);

drawarrow(sort1, ssort1);
drawarrow(sort2, ssort1);
drawarrow(sort3, ssort1);

drawarrow(ssort1, so_on);
