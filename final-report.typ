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
However, the Mathematica notebook only covers a part of the paper's content, and most proofs are not formally verified.
At the same time, the paper is very constructive, in the sense that most proofs either state properties of existing objects, or construct new objects with certain properties.
This makes it very suitable for the process of formal verification.

For this project, I have decided to write a formal verification of part 1 (Section 2) of Brendle and Hung's paper, in the Lean 4 proof assistant.
Ideally, the entire paper should be formalized.

This has multiple benefits:
- A formally verified proof is a computer program that represents the entire line of reasoning all the way down to the axioms of mathematics. It is therefore of the highest rigor.
- Lean 4 is a programming language that allows extensive manipulation and analysis of mathematical objects, propositions, and proofs. Stating the results of the paper in this language allows us to inspect them programmatically and potentially simplify them.
- Formalization means, in particular, that all assumptions made to prove a result are explicitly stated. We may then reduce these assumptions by removing redundancies, and try to generalize the arguments made in the paper.

We will begin with an overview of how dependent types and proof assistants work.

= Type theory and proof assistants
// #let ta = math.op(":")

== Motivation

Under the standard Zermelo-Frenkel axiomatic system, all objects in mathematics are sets.
However, this is not how we think about them.
The object $2$ is a _natural number,_ $pi$ is a _real number,_ and $x |-> 2x$ is a _function._
It is weird to say that all of them are actually of the same kind.

Moreover, this notion that "everything is a set" may lead to "accidental equalities".
Nothing stops two completely unrelated objects from being "equal" when viewed in detail.
For example, it may be that the Banach space $L^2 (RR)$ happens to be equal, as a set, to the Cartesian product of the Riemann $zeta$-function with the Cantor set.

The main idea of type theory is to introduce a binary relation $(:)$ between objects (which we will also call _terms_). The proposition $a : A$ means that _term $a$ has type $A$._ Note that types are themselves also terms.

In type theory, every term must have a type. This means that the type $A$ must also have a type. Since $A$ _is_ a type, we can create a new term called $"Type"$ and write $A : "Type"$. This term $"Type"$, however, must also have a type, and so on.

To ensure that all terms have a type, one of the usual axioms of type theory is the existence of an infinite sequence of "universes"
$
  U_1 : U_2 : U_3 : U_4 : ...
$
such that $U_i$ has type $U_(i+1)$ for all $i in NN$. We can then define a term $A$ to be a _type,_ if $A : U_k$ for some $k$. Since every term must have a type, we see that for every term $a$ there is a term $A$ and index $k in NN$ such that $a : A : U_k$.

== The Calculus of Types

Types can be combined to produce new types in the following ways:
- If $A$ and $B$ are types, the expression $A -> B$ denotes the _function type_ from $A$ to $B$. A term $f : A -> B$ is defined as a function: for all terms $a : A$, one must have a term $f(a) : B$.
- If $A, B$ are types, the type $A times B$ is the _product type,_ which corresponds to the notion of Cartesian product. Terms of type $A times B$ are pairs $(a,b)$, where $a : A$ and $b : B$.
- If $A, B$ are types, there is a _sum type_ $A union.sq B$, which corresponds to the notion of disjoint union. Terms of type $A union.sq B$ are defined as follows:
  + For every term $a : A$, we have a term $op("inl") a : A union.sq B$;
  + For every term $b : B$, we have a term $op("inr") b : A union.sq B$;

#figure(
  caption: [A tree representation of typing relations],
  image("figures/type-tree.pdf")
) <tree>

Since types are also terms, we may go beyond the standard intuition of functions.

Let $A$ be a type and let $B : A -> U_k$ be a function from $A$ to $U_k$ for some $k$. That is to say, $B$ takes in a term of type $A$ and returns another type.
Now, we define the type $product_(a : A) B(a)$ of _dependent functions._ To give a term $f : product_(a : A) B(a)$, one has to give a function that for each term $a : A$, gives a term $f(a) : B(a)$. Such functions are called _dependent_ because the type of the output depends on the type of the input.

If the function $B$ is constant, $B(a) = B_0$, then a dependent function $f : product_(a : A) B(a)$ becomes a regular function $f : A -> B_0$.

Consider $A = {0,1}$, where ${0,1}$ is a type that has exactly two terms, $0 : {0,1}$ and $1 : {0,1}$. Then the type $product_(a : A) B(a)$ is equivalent to the product type $B(0) times B(1)$.

Similarly, given a type $A$ and a function $B : A -> U_k$, we introduce the _dependent pair type_ written as $sum_(a : A) B(a)$. Terms of this type are pairs $(a, b)$ where $b : B(a)$. They are called dependent pairs because the type of the second element depends on the first element.

There are other operations on types, but we will not consider them here, for the sake of simplicity.

With these operations, our type system becomes a rich algebraic structure, and we can represent it as a tree, as seen in @tree.

== Propositions as Types

There is a correspondence between propositions and types. For every proposition $P$, we can define a type $tau(P)$, and a term $a$ will have type $tau(P)$ if it is a "proof" of the proposition $P$. This way, true propositions correspond to _inhabited_ ("non-empty") types, while false propositions are mapped to _uninhabited_ ("empty") types.

The reason why this identification is so powerful lies in the correspondence between logical operations and type operations. In what follows, let $P, Q$ be propositions.
- We have $tau(P => Q) = tau(P) -> tau(Q)$. Indeed, the statement "if $P$ is true, then $Q$ is true" is translated to "if $P$ has a proof, then $Q$ must have a proof", which, in turn, is equivalent to "there is a function that, given a proof of $P$, produces a proof of $Q$".
- We have $tau(P and Q) = tau(P) times tau(Q)$. Indeed, to produce a proof of $P and Q$, one must produce a proof of $P$ and a proof of $Q$, i.e. a _pair_ of proofs, hence the product type.
- Similarly, we have $tau(P or Q) = tau(P) union.sq tau()$

But the correspondence goes further. Consider a predicate $P(x)$. Then we have
$
  tau(forall x in RR wh P(x)) = product_(x : "Real") tau(P(x)).
$
Indeed, to produce a proof of $forall x in RR wh P(x)$, it suffices to give a function that for all $x : "Real"$ produces a proof of $P(x)$.

Similarly, existence propositions correspond to dependent pair types:
$
  tau(exists x in RR wh P(x)) = sum_(x : "Real") tau(P(x)).
$

These observations imply that our algebra of terms has a model of propositional logic inside it.
As a result, propositions may be specified as types in a programming language, and proofs can be written for them as terms in the same programming language.

== An Overview of the Lean Programming Language

Lean is a programming language that implements the type system described above. A _program_ in Lean is a sequence of term definitions. For example, natural numbers may be defined in Lean as follows:
```lean
inductive Nat
| Z
| S (n : Nat)
```

This creates the terms `Z`, `(S Z)`, `(S (S Z))`, ..., as well as the type `Nat` that unites all these terms. For each of these terms, we have a typing sequence
$
  S thin (S thin Z) : "Nat" : ("Sort 1") : ("Sort 2") : ("Sort 3") : ...
$
Here, `Sort n` is the Lean notation for the type universe $U_n$.

= Results

== Multivariable Taylor Approximations

== Euclidean Framework

== Generalization to Riemannian Manifolds

= Conclusion
