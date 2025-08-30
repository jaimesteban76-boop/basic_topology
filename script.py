
def strip_proofs(lines: list) -> list:
    import re
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"(\s*)(theorem|lemma|example)\b.*(:=\s*by|:=\s*{)", line)
        if m:
            indent = m.group(1)
            header = re.split(r":=", line, 1)[0].rstrip()
            new_lines.append(header + " := by\n")
            new_lines.append(indent + "  sorry\n")
            i += 1
            while i < len(lines) and lines[i].strip() != "" and not re.match(r"\s*(theorem|lemma|example|def|structure)\b", lines[i]):
                i += 1
            continue
        new_lines.append(line)
        i += 1
    return new_lines

def parse_text(x: str) -> str:
    import urllib.parse
    return urllib.parse.quote(x, safe="")

def parse_text_lz(x: str) -> str:
    from lzstring import LZString
    lz = LZString()
    return lz.compressToEncodedURIComponent(x)

if __name__ == "__main__":
    with open("./BasicTopology/Basic.lean", "r", encoding="utf-8") as f:
        basic_lines = f.readlines()
    
    exercises_lines = strip_proofs(basic_lines)
    
    with open("./BasicTopology/Exercises.lean", "w", encoding="utf-8") as f:
        f.writelines(exercises_lines)

    basic = "".join(basic_lines)
    exercises = "".join(exercises_lines)

    basic_parsed = parse_text_lz(basic)
    exercises_parsed = parse_text_lz(exercises)

    readme = f"""
Some basic point-set topology in Lean for fun.

There is an automatically generated file called `Exercises.lean` with proofs of theorems removed if you want to try yourself :)

I also copied the code into clickable links to the Lean 4 Web server. Love that place
- [Link to main file](https://live.lean-lang.org/#codez={basic_parsed}) (slow)
- [Linked to exercises](https://live.lean-lang.org/#codez={exercises_parsed})
    """
    readme = readme.strip()
    with open("./README.md", "w") as f:
        f.write(readme)