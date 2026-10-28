// @vitest-environment node
// The papers shelf shows each PDF's real first page, rendered by
// scripts/render-paper-pages.py. A picture is shown only while it matches its PDF;
// this test fails when a re-rendered PDF has made a picture stale, so the shelf is
// refreshed in the same change as the paper.
import { describe, expect, it } from "vitest";
import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { PAPER_PDFS as PAGES } from "virtual:paper-pdfs";
import { PAPER_PDFS, PAPER_PAGES } from "../vite.config";

const site = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const FIX = "run python site/scripts/render-paper-pages.py from the repository root";

describe("the papers' first pages", () => {
  const manifest = JSON.parse(readFileSync(path.join(site, PAPER_PAGES, "manifest.json"), "utf8"));

  it.each(Object.entries(PAPER_PDFS))("%s has a current picture of its first page", (stage, pdf) => {
    const row = manifest[stage];
    expect(row, `no picture for ${pdf.file}; ${FIX}`).toBeDefined();
    const digest = `sha256:${createHash("sha256").update(readFileSync(path.join(site, pdf.file))).digest("hex")}`;
    expect(row.pdf_sha256, `${pdf.file} changed since its picture was rendered; ${FIX}`).toBe(digest);
    for (const file of Object.values(row.files as Record<string, string>)) {
      expect(existsSync(path.join(site, PAPER_PAGES, file)), file).toBe(true);
    }
  });

  it("reaches the shelf through the PDFs' build-time module, with both widths", () => {
    for (const [stage, entry] of Object.entries(PAGES)) {
      expect(entry.firstPage, stage).toBeDefined();
      expect(entry.firstPage!.srcSet).toMatch(/ 176w, .* 352w$/);
      expect(entry.firstPage!.src).toMatch(/^paper-pages\/.*-352\.webp$/);
      expect(entry.firstPage!.width / entry.firstPage!.height).toBeCloseTo(612 / 792, 2);
    }
  });
});
