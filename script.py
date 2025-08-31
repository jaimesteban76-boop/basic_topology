import re

def strip_proofs(lines: list) -> list:
    output = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"(\s*)(theorem|lemma|example)\b.*(:=\s*by|:=\s*{)", line)
        if m:
            indent = m.group(1)
            header = re.split(r":=", line, 1)[0].rstrip()
            output.append(header + " := by\n")
            output.append(indent + "  sorry\n")
            i += 1
            while i < len(lines) and lines[i].strip() != "" and not re.match(r"\s*(theorem|lemma|example|def|structure)\b", lines[i]):
                i += 1
            continue
        output.append(line)
        i += 1
    return output

if __name__ == "__main__":
    with open("./basic_topology/basic.lean", "r", encoding="utf-8") as f:
        basic = f.readlines()
    
    exercise = strip_proofs(basic)
    
    with open("./basic_topology/exercise.lean", "w", encoding="utf-8") as f:
        f.writelines(exercise)
