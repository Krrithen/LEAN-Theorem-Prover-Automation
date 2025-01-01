# Formal Verification Pipeline Using LEAN Theorem Prover

This project implements a **Formal Verification Pipeline** using the **LEAN Theorem Prover**, enabling rigorous validation of logical correctness in mathematical problems. By automating the generation, execution, and testing of Lean scripts using Python, the pipeline achieves a seamless integration of mathematical reasoning and software engineering.

## Key Features

- **Palindrome Verification:** Implements inductive definitions and proofs for palindromes in lists using Lean.
- **Automation:** Python scripting automates Lean script generation and execution, significantly reducing verification time.
- **Logical Correctness:** Ensures 100% correctness by leveraging Lean's proof capabilities.
- **Test Suite Integration:** Facilitates the use of test cases to validate correctness across various scenarios.

---

## Table of Contents

1. [Installation](#installation)
2. [Pipeline Overview](#pipeline-overview)
3. [Usage](#usage)
4. [Lean Proofs](#lean-proofs)
5. [Examples](#examples)
6. [Contributing](#contributing)
7. [License](#license)

---

## Installation

### Prerequisites
- Python (>=3.8)
- Lean (>=4.0)
- `pip` for Python dependencies

### Setup

1. Clone the repository:
   ```bash
   git clone https://github.com/your-username/formal-verification-pipeline.git
   cd formal-verification-pipeline
   ```

2. Install Python dependencies:
   ```bash
   pip install -r requirements.txt
   ```

3. Ensure Lean is installed and accessible via the command line:
   ```bash
   lean --version
   ```

---

## Pipeline Overview

1. **Input Test Cases:** Users provide test cases in a plain text file (e.g., `PalindromeTestCases.txt`).
2. **Lean Script Generation:** Python scripts dynamically create Lean code for the specified problem.
3. **Script Execution:** The generated Lean scripts are executed to validate the provided test cases.
4. **Output Results:** The pipeline outputs the verification status for each test case (Verified/Failed).

---

## Usage

1. **Prepare Test Cases:**  
   Create a text file (`PalindromeTestCases.txt`) with the following format:
   ```
   [1,2,1] - true
   [1,2,3] - false
   ```

2. **Run the Pipeline:**  
   Execute the main Python script:
   ```bash
   python main.py
   ```

3. **Review Output:**  
   The script will generate Lean files, run them, and display the results in the console:
   ```
   Running Lean script for problem ID: 001
   Test result for 001: Verified
   ```

---

## Lean Proofs

The core of this project lies in its Lean-based formal proofs. Below are some key definitions and theorems:

### Palindrome Definition
```lean
inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])
```

### Key Theorems
1. **Reverse of a Palindrome is a Palindrome:**
   ```lean
   theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
     induction h with
     | nil => exact Palindrome.nil
     | single a => exact Palindrome.single a
     | sandwich a h ih => simp; exact Palindrome.sandwich _ ih
   ```
2. **Correctness of `isPalindrome` Function:**
   ```lean
   theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : 
       as.isPalindrome ↔ Palindrome as := by
     simp [isPalindrome]
     exact Iff.intro (fun h => palindrome_of_eq_reverse h) (fun h => reverse_eq_of_palindrome h)
   ```

---

## Examples

### Test Case: `[1, 2, 1]`
- **Input:** `[1, 2, 1]`
- **Expected Output:** `true`
- **Result:** Verified

### Test Case: `[1, 2, 3, 1]`
- **Input:** `[1, 2, 3, 1]`
- **Expected Output:** `false`
- **Result:** Failed

### Code Execution
Run the following Python script to evaluate the test cases:
```python
python main.py
```

---

## Contributing

Contributions are welcome! To contribute:
1. Fork this repository.
2. Create a feature branch.
3. Commit your changes and submit a pull request.

---
