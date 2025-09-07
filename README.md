# Logic Problem Solver

**Logic Problem Solver** is a web app that evaluates propositional logic arguments using truth tables and natural deduction. It provides step-by-step derivations and color-coded verdicts for valid or invalid conclusions.

## Features

- Input multiple premises and a single conclusion.
- Supports propositional operators: `->` (implication), `&` (and), `|` (or), `~` (not), and parentheses `()`.
- Step-by-step natural deduction derivations (forward-chaining rules).
- Truth-table verification for exhaustive validation.
- Color-coded verdicts: ✅ Valid, ❌ Invalid, ⚠️ Premises inconsistent.
- Load example problems and clear inputs easily.

## Usage

1. Enter premises (one per line) and a conclusion.
2. Click **Solve** to see:
   - Truth table
   - Natural deduction steps (if derivable)
   - Overall validity
3. Click **Load Example** to auto-fill an example problem.
4. Click **Clear** to reset inputs and outputs.

### Example

  **Premises:**
  ```
  (P | Q) -> R
  P
  ~R
  ```
  
  **Conclusion:**
  ``` ~Q ```

**Result:**
- Truth table shows validity/invalidity.
- Step-by-step derivation `if` possible.

## Installation / Hosting

- Open `index.html` in any modern browser (Chrome, Firefox, Edge).
- Purely client-side; no backend required.

## Testing & Limits

- Works best for small to medium propositional expressions.
- Extremely complex expressions may exceed natural deduction engine limits.
- Recommended to test using known valid/invalid examples.

## Future Improvements

- Implement proof by contradiction and full conditional derivation for more natural deduction coverage.
- Allow multi-conclusion derivations.
- Export derivation steps as PDF or LaTeX.
- Extend support to predicate logic.

## License

MIT License — free to use and modify.

## Credits
``` 
- ChatGPT for debugging errors in the code :)
- Heet Parikh
``` 
