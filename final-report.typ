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

= Introduction and structure

Let $(M, g)$ be a Riemannian manifold. The _sectional curvature_ at point $p in M$ is defined for a given 2-plane $pi subset T_p M$ as
$
  K_g (pi) := (R_g (X, Y, Y, X))/(g(X,X) g(Y,Y) - g(X,Y)^2)
$
In 2-manifolds, the above coincides with the Gauss curvature.
The round sphere $SS^2$ has a constant Gauss curvature of 1, and one can easily see that the sectional curvature of $M = SS^2 times SS^2$, under the standard product metric, is non-negative for any 2-plane $pi subset T_p M$.
However, it vanishes for tangent planes that combine vectors from the tangent spaces of both $SS^2$ factors.
A natural question (posed by Hopf) is whether a metric exists on $SS^2 times SS^2$ whose sectional curvature is strictly positive for all tangent 2-planes. Brendle and Hung (2026) have answered this question in the positive.

The paper is structured as follows:
/ Section 2: 
