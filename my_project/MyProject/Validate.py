import os
import subprocess

def generate_lean_script(problem): 
    """Generates a Lean script for the given problem."""
    template = f"""

    -- Inductive definition for Palindrome
    inductive Palindrome : List α → Prop where
      | nil      : Palindrome []
      | single   : (a : α) → Palindrome [a]
      | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

    -- Prove that the reverse of a palindrome is a palindrome
    theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
      induction h with
      | nil => exact Palindrome.nil
      | single a => exact Palindrome.single a
      | sandwich a h ih => simp; exact Palindrome.sandwich _ ih

    -- Prove that if a list is a palindrome, its reverse is equal to itself
    theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
      induction h with
      | nil => rfl
      | single a => rfl
      | sandwich a h ih => simp [ih]

    -- Example using reverse_eq_of_palindrome
    example (h : Palindrome as) : Palindrome as.reverse := by
      simp [reverse_eq_of_palindrome h, h]

    -- Function to find the last element of a non-empty list
    def List.last : (as : List α) → as ≠ [] → α
      | [a],         _ => a
      | _::a₂::as, _ => (a₂::as).last (by simp)

    -- Theorem for appending the last element back to the list
    @[simp] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
      match as with
      | [] => contradiction
      | [a] => simp_all [last, dropLast]
      | a₁ :: a₂ :: as =>
        simp [last, dropLast]
        exact dropLast_append_last (as := a₂ :: as) (by simp)

    -- Auxiliary induction principle for lists
    theorem List.palindrome_ind (motive : List α → Prop)
        (h₁ : motive [])
        (h₂ : (a : α) → motive [a])
        (h₃ : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
        (as : List α)
        : motive as :=
      match as with
      | []  => h₁
      | [a] => h₂ a
      | a₁::a₂::as' =>
        have ih := palindrome_ind motive h₁ h₂ h₃ (a₂::as').dropLast
        have : [a₁] ++ (a₂::as').dropLast ++ [(a₂::as').last (by simp)] = a₁::a₂::as' := by simp
        this ▸ h₃ _ _ _ ih
    termination_by as.length

    -- Prove that if a list is equal to its reverse, it is a palindrome
    theorem List.palindrome_of_eq_reverse (h : as.reverse = as) : Palindrome as := by
      induction as using palindrome_ind
      next   => exact Palindrome.nil
      next a => exact Palindrome.single a
      next a b as ih =>
        have : a = b := by simp_all
        subst this
        have : as.reverse = as := by simp_all
        exact Palindrome.sandwich a (ih this)

    -- Function to check if a list is a palindrome
    def List.isPalindrome [DecidableEq α] (as : List α) : Bool :=
        as.reverse = as

    -- Prove the correctness of isPalindrome
    theorem List.isPalindrome_correct [DecidableEq α] (as : List α) : as.isPalindrome ↔ Palindrome as := by
      simp [isPalindrome]
      exact Iff.intro (fun h => palindrome_of_eq_reverse h) (fun h => reverse_eq_of_palindrome h)

    -- Evaluate the test case
    #eval {problem['input']}.isPalindrome ↔ {problem['expected_result']}
    """
    return template

def read_test_cases(file_path):
    """Reads test cases from a text file and formats them."""
    test_cases = []
    with open(file_path, 'r') as file:
        lines = file.readlines()
        for idx, line in enumerate(lines):
            input_value, expected_result = line.strip().split('-')
            test_case = {
                "problem_id": f"{idx+1:03}",  # Generate 001, 002, etc.
                "input": input_value.strip(),
                "expected_result": expected_result.strip()
            }
            test_cases.append(test_case)
    return test_cases


def save_script(script_content, folder_path, file_name):
    """Saves the generated Lean script to a file inside the specified folder."""
    os.makedirs(folder_path, exist_ok=True)  # Ensure folder exists
    file_path = os.path.join(folder_path, file_name)
    with open(file_path, 'w') as file:
        file.write(script_content)
    return file_path

def run_lean(file_path):
    """Runs the Lean script and captures its output."""
    result = subprocess.run(["lean", file_path], capture_output=True, text=True)
    return result.stdout, result.stderr

def parse_output(output):
    """Parses Lean output to determine test status."""
    if "true" in output.lower():
        return "Verified"
    elif "false" in output.lower():
        return "Failed"
    else:
        return "Unknown"

def main():
    # Folder for Lean test case files
    folder_name = "PalindromeLeanScripts"
    
    # Path to the text file with test cases
    test_cases_file = "PalindromeTestCases.txt"
    
    # Read and parse test cases from the file
    test_cases = read_test_cases(test_cases_file)

    # Process each test case
    for case in test_cases:
        # Generate the script
        script_content = generate_lean_script(case)
        file_name = f"{case['problem_id']}.lean"

        # Save the script to the specified folder
        file_path = save_script(script_content, folder_name, file_name)
        print(f"Running Lean script for problem ID: {case['problem_id']}")
        
        # Run Lean on the generated script
        stdout, stderr = run_lean(file_path)
        
        # Parse the output
        status = parse_output(stdout + stderr)
        print(f"Test result for {case['problem_id']}: {status}")
        
        if status == "Failed":
            print("Error details:")
            print(stderr)

if __name__ == "__main__":
    main()