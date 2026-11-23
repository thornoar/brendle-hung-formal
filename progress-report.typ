#import "@local/templates:0.0.0": *
#import "@local/common:0.0.0": *

// #set page(numbering: none)
#show: assignment-title-rule(
  title: [SCIE3500 Progress Report: Metrics With Positive Curvature],
  due: [Fri, Oct 16],
  header: [Metrics of Positive Sectional Curvature #h(1fr) SCIE3500 Progress Report],
  ext1: [Supervisor: FONG, Tsz-Ho Frederick],
  fontsize: 14pt,
)

#set heading(numbering: "1.")

= Background

My project builds on a recent paper @brendle by Simon Brendle and Pei-Ken Hung, in which they construct a metric on $SS^2 times SS^2$ with positive sectional curvature. The main motivation is a previous result @kleiner by Hsiang and Kleiner, in which is was established that an orientable 4-manifold with positive sectional curvature that admits a non-trivial Killing vector field must be homeomorphic to $SS^4$ or $CC PP^2$. Since $SS^2 times SS^2$ is homeomorphic to neither, we can conclude that a metric on $SS^2 times SS^2$ with positive sectional curvature cannot admit a non-trivial Killing field.

Furthermore, Brendle and Hung's result gives weak evidence to one of the Hopf conjectures, which states that an even-dimensional compact Riemannian manifold with positive sectional curvature has positive Euler characteristic.

= Research goals

To study the paper extensively and produce a generalization of some of its results.

= Current project state

At this time I am at the reading stage, both in terms of background in Riemannian geometry, and in terms of specific constructions central to the paper, such as the Cheeger @cheeger metric.

#bibliography("bib.yml")
