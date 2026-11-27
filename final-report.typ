#import "@local/templates:0.0.0": *
#import "@local/common:0.0.0": *

// #set page(numbering: none)
#show: assignment-title-rule(
  title: [SCIE3500 Final Report: A Metric on $SS^2 times SS^2$ with Positive Sectional Curvature],
  name: "Roman Maksimovich",
  due: none,
  header: [A Metric on $SS^2 times SS^2$ with Positive Sectional Curvature #h(1fr) SCIE3500 Final Report],
  ext1: [Supervisor: FONG, Tsz-Ho Frederick],
  fontsize: 14pt,
  textsize: 11pt,
  fontname: "TeX Gyre Schola",
  inset: (left: 8pt, bottom: 10pt, top: 1pt),
)
#set heading(numbering: "1.")

#outline()

= Introduction

== Background

Let $(M, g)$ be a Riemannian manifold. The _sectional curvature_ at point $p in M$ is defined for a given 2-plane $pi subset T_p M$ as
$
  K_g (pi) := (R_g (X, Y, Y, X))/(g(X,X) g(Y,Y) - g(X,Y)^2)
$
In 2-manifolds, the above coincides with the Gauss curvature.
The round sphere $SS^2$ has a constant Gauss curvature of 1, and one can easily see that the sectional curvature of $M = SS^2 times SS^2$, under the standard product metric, is non-negative for any 2-plane $pi subset T_p M$.
However, it vanishes for tangent planes that combine vectors from the tangent spaces of both $SS^2$ factors.
A natural question (posed by Hopf) is whether a metric exists on $SS^2 times SS^2$ whose sectional curvature is strictly positive for all tangent 2-planes. Brendle and Hung (2026) have answered this question in the positive, with a third-order perturbation of a well-studied Cheeger-Müter metric.

== The structure of the paper

The paper is divided into the following logical parts:
+ An abstract framework concerned with an arbitrary smooth function $u : overline(B^m_(r_0)) times overline(B^n_(r_0)) times [-s_0, s_0] -> RR$, where the authors develop tools to guarantee, under certain conditions, that the minimum
  $
    f(s) = min_(y in A) min_(w in overline(B^n_(r_0))) u(y, w, s)
  $
  is positive for sufficiently small $s$, where $A$ is a suitable compact subset of $overline(B^m_(r_0))$.
+ A generalization of this result to the case of a compact Riemannian manifold $cal(N)$ and smooth function $u : cal(N) times [-s_0, s_0] -> RR$. The main statement is Theorem 2.12 which states that under certain extensive conditions, the minimum $min_(p in cal(N)) u(p, s)$ is strictly positive for small $s$.
+ An explicit calculation of the Cheeger-Müter metric on $M$, constructed from the standard product metric using the diagonal action of $S O (3)$ on $SS^2 times SS^2$.
+ A set of abstract tools for manipulating second-order perturbations of the Cheeger-Müter metric $g$. These tools rely on the abstract Euclidean framework constructed in part 1.
+ A concrete second order perturbation $g_s = g + s h^((1)) + s^2 h^((2))$ of the metric $g$. The sectional curvature of this metric is strictly positive everywhere on $M$ except for a certain 2D torus $Sigma subset M$.
+ A discussion of the properties of the functions $v$, $v^((i))$, and $V^((i))$ that are defined based on the metric $g_s$. The main results are properties of the function $V^((3)) : Sigma -> RR$ which has a non-vanishing integral over $Sigma inter M_"nondeg"$ if two real constants are suitably chosen.
+ A third-order perturbation $tilde(g)_s := g_s + s^3 h^((3))$. Here, $h^((3))$ is defined based on the properties of $V^((3))$ proved in the previous part.
+ A proof that there exists a real number $s$ such that $tilde(g)_s$ has positive sectional curvature on all of $M$. This proof utilizes theorem 2.12 of part 2.

== The aim of this project

Despite having clear substance, Brendle and Hung's paper is notoriously hard to understand, and their calculations convolute the mind like nothing else.
Some of them were even made using Wolfram Mathematica, in order to speed up the calculation process and to verify the results.

