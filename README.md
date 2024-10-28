# Trust boundary problems with AlloyMax

### Model files
- tb5.als is the latest AlloyMax for the trust boundary problems.
- The other *.thm files are the visualization configs for solutions.

### Problems
There are different `run` commands in the model file corresponding to different trust boundary related problems.

#### Compute trust boundary
`TB1` and `TB2` are two problems for computing the trust boundaries for `monitorPatient` and `billManagement`, respectively. Running the two problems can generate the trust boundary for a given requirement.

For example, running `TB1` generate the trust boundary for the requirement defined by `monitorPatient` predicate. Also, the user can load `TB1view.thm` for a better visual presentation.

#### Adaptation under attack
`Adaptation` command defines a runtime adaptation problem where a set of components (e.g., PatientRecord) are compromised, then the problem tries to find a new architecture where a set of requirements (predicates) can continue to be available (satisfied). In particular, we allow the introduction of new components and connections. Also, we use AlloyMax to minimize the number of new components and the difference between the new architecture and the old one.

The user can also load `AdaptationView.thm` for a better visualization.

#### Redesign with no overlapping trust boundaries
`NoOverlap` command defines a redesign problem. The idea is that one tactic to improve the security and resillience of a system is to have on (or minimal) overlapping trust boundaries among requirements. So here we show an example of it to generate a new architecture where the `monitorPatient` requirement and the `billManagement` requirement should not have overlapping trust boundaries. In particular, we allow the introduction of new components and connections. Also, we use AlloyMax to minimize the number of new components and the difference between the new architecture and the old one.

The user can also load `NoOverlapView.thm` for a better visualization.