import katex from "katex";
import { describe, expect, it } from "vitest";
import { breakForms, independentFormulas, relationLines, splitDisplay, sumRuns } from "../src/reader/texBreaks";

const renders = (tex: string) => katex.renderToString(tex, { displayMode: true, throwOnError: true, strict: "ignore" });

// Euler (1.2), as the paper writes it.
const EULER_1_2 = `\\begin{equation}
 \\int_0^{T_*}\\|\\nabla u(t)\\|_{L^\\infty}\\,\\mathrm dt=\\infty,
 \\qquad
 \\int_0^{T_*}\\|\\operatorname{curl}u(t)\\|_{L^\\infty}\\,\\mathrm dt=\\infty. \\tag{1.2}
\\end{equation}`;

describe("a display's number and outer environment", () => {
  it("takes the equation environment, the number and any label off the formula", () => {
    const { body, tag } = splitDisplay("\\begin{equation} a=b \\label{eq:x} \\tag{5.43}\\end{equation}");
    expect(body).toBe("a=b");
    expect(tag).toBe("\\tag{5.43}");
  });

  it("leaves a \\tag inside braces alone", () => {
    expect(splitDisplay("x_{\\tag{1}} = y").tag).toBeNull();
  });
});

describe("independent formulas", () => {
  it("splits Euler (1.2) at its comma and \\qquad, keeping the comma", () => {
    const parts = independentFormulas(splitDisplay(EULER_1_2).body);
    expect(parts).toHaveLength(2);
    expect(parts[0].endsWith("=\\infty,")).toBe(true);
    expect(parts[1].startsWith("\\int_0^{T_*}\\|\\operatorname{curl}")).toBe(true);
  });

  it("needs a quad after the comma, and never splits inside braces, \\left…\\right or an environment", () => {
    expect(independentFormulas("f(a, b) = c")).toHaveLength(1);
    expect(independentFormulas("x_{a,\\qquad b} = c")).toHaveLength(1);
    expect(independentFormulas("\\left( a,\\qquad b \\right) = c")).toHaveLength(1);
    expect(independentFormulas("\\begin{cases} a,\\qquad b \\end{cases} = c")).toHaveLength(1);
    expect(independentFormulas("a = 1,\\quad b = 2;\\qquad c = 3")).toEqual(["a = 1,", "b = 2;", "c = 3"]);
  });
});

describe("relation lines", () => {
  it("breaks before each top-level relation, keeping the left side on the first line", () => {
    expect(relationLines("A = B + C \\le D < E")).toEqual({ left: "A", rights: ["= B + C", "\\le D", "< E"] });
  });

  it("ignores relations inside braces, brackets, \\left…\\right and environments", () => {
    expect(relationLines("\\sum_{j=1}^{n} a_j = \\left( x = y \\right) + f(t<1) + \\{s : s=1\\} + \\begin{cases} 1 & x=0 \\end{cases}").rights).toHaveLength(1);
  });

  it("keeps := together", () => {
    expect(relationLines("F := G = H")).toEqual({ left: "F", rights: [":= G", "= H"] });
  });
});

describe("runs at plus and minus", () => {
  it("splits only at binary signs at depth zero", () => {
    expect(sumRuns("= a + b - c + d", 2)).toEqual(["= a + b", "- c + d"]);
    expect(sumRuns("-a + (b + c)", 2)).toEqual(["-a", "+ (b + c)"]);
    expect(sumRuns("{a + b} + \\left[c - d\\right]", 2)).toEqual(["{a + b}", "+ \\left[c - d\\right]"]);
    expect(sumRuns("a = -b", 2)).toEqual(["a = -b"]);
    expect(sumRuns("x^{-1} \\cdot y", 2)).toEqual(["x^{-1} \\cdot y"]);
  });
});

describe("the broken forms", () => {
  it("stacks Euler (1.2) first, with its number on the last line, and every form renders", () => {
    const forms = breakForms(EULER_1_2);
    expect(forms[0]).toMatch(/^\\begin\{gather\*\}.*=\\infty,\\\\\{\}.*=\\infty\.\s*\\tag\{1\.2\}\\end\{gather\*\}$/s);
    for (const form of forms) expect(() => renders(form)).not.toThrow();
  });

  it("aligns relation lines and hangs a long sum under them", () => {
    const forms = breakForms("A = B + C + D + E \\le F");
    expect(forms[0]).toBe("\\begin{align*}A&= B + C + D + E\\\\{}&\\le F\\end{align*}");
    expect(forms[1]).toContain("\\\\{}&\\qquad{}+");
    for (const form of forms) expect(() => renders(form)).not.toThrow();
  });

  it("has none for a formula without a top-level break, or one already laid out in lines", () => {
    expect(breakForms("\\frac{a+b}{c=d}")).toEqual([]);
    expect(breakForms("\\begin{aligned} a &= b \\\\ &= c \\end{aligned}")).toEqual([]);
    expect(breakForms("a &= b \\\\ c &= d")).toEqual([]);
  });
});
