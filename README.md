# von Neumann-Morgenstern Utility Theorem in Lean 4

This repository contains a formalization of the von Neumann-Morgenstern (vNM) utility theorem in the Lean 4 theorem prover. The formalization demonstrates how the axioms of expected utility theory lead to the existence of a utility function that represents a preference relation over lotteries.

## Overview

The von Neumann-Morgenstern utility theorem is a foundational result in decision theory and economics, establishing that under certain axioms of rational choice, an agent's preferences over lotteries (probabilistic outcomes) can be represented by the expected value of a utility function.

This formalization includes:
- Definitions of preference relations and lotteries
- Formalization of the vNM axioms:
  - Completeness
  - Transitivity
  - Continuity
  - Independence
- Proof of the main theorem
- Examples and applications

## Documentation

The LaTeX documentation in the `tex/` directory provides detailed explanations of:
- The mathematical formulation of the vNM theorem
- How the formalization maps to the traditional presentation
- Details on key proof techniques used
- Extensions and variations of the theorem

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request or create an Issue if you find any problems or have suggestions for improvements.

## License

See the LICENSE file for details.

## Acknowledgments

- The formalization builds on the probability theory components from Mathlib
- Thanks to the Lean community for their support and foundational work
```
