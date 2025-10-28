Point-set topology in Lean 4.

Loosely based on General Topology by Willard (1970).

View the main file on Lean 4 web server: [Link](https://live.lean-lang.org/#url=https://github.com/mdnestor/basic_topology/blob/master/basic_topology/T0_topology.lean)

Dependency graph:

```mermaid
graph LR

Topology --> Basis
Metric --> Bounded
Mathlib --> Bounded
Subspace --> Compact
Sequence --> Compact
Metric --> Complete
Sequence --> Complete
Continuity --> Connected
Operations --> Continuity
Operations --> Dense
Relation --> Homeomorphism
Continuity --> Homeomorphism
Mathlib --> Metric
Metric --> MetricTopology
Continuity --> MetricTopology
Topology --> Neighborhood
Relation --> Net
Relation --> Continuity
Basis --> Operations
Neighborhood --> Operations
Operations --> Product
Net --> Separation
Product --> Separation
Metric --> Separation
Dense --> Separation
Separation --> Sequence
MetricTopology --> Sequence
Topology --> Subspace
Mathlib --> Topology

```

<div align="center">
  <img src="https://upload.wikimedia.org/wikipedia/commons/e/e1/Runge_theorem.svg" width="25%">
</div>
