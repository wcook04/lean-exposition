#!/usr/bin/env python3
"""Capture the front page's five pictures of the site in use (public/stills/tour-*.webp).

Each picture is the real page at 1440x790, in the light and the dark scheme, saved 1440 and
2880 pixels wide. Run it against a served static edition after a change to the reader, the
Compare page or the What ran page, then look at every picture before committing them:

    python site/scripts/capture-tour-stills.py http://localhost:5179/

It needs Playwright for Python with Chromium, and cwebp on the PATH.
"""

from __future__ import annotations

import asyncio
import subprocess
import sys
import tempfile
from pathlib import Path

from playwright.async_api import Page, async_playwright

OUT = Path(__file__).resolve().parents[1] / "public" / "stills"
WIDTH, HEIGHT = 1440, 790
# The card a reader clicks in the third picture, by the words on it.
CARD = "Controlled diffusion"


async def settle(page: Page, ms: int = 1800) -> None:
    await page.evaluate("document.fonts.ready")
    await page.wait_for_timeout(ms)


async def scroll_paper(page: Page) -> None:
    await page.mouse.move(400, 500)
    await page.mouse.wheel(0, 6000)
    await settle(page)


async def follow(page: Page, base: str) -> None:
    await page.goto(base + "read/expository/")
    await settle(page, 2600)
    await scroll_paper(page)
    await page.mouse.move(720, 28)
    await settle(page, 900)


async def tick(page: Page, base: str) -> None:
    await page.goto(base)
    await settle(page)
    href = await page.locator(".front__guide-link a").get_attribute("href")
    await page.goto(base.rstrip("/") + href[href.index("/read") :] if href and "/read" in href else base + "read/short")
    await settle(page, 3200)


async def card(page: Page, base: str) -> None:
    await follow(page, base)
    box = await page.get_by_text(CARD).last.bounding_box()
    if not box:
        raise SystemExit(f'no card "{CARD}" on the graph')
    await page.mouse.click(box["x"] + box["width"] / 2, box["y"] + box["height"] / 2)
    await settle(page, 2400)
    await page.mouse.move(720, 28)
    await settle(page, 900)


async def compare(page: Page, base: str) -> None:
    await page.goto(base + "compare?n=full_support")
    await settle(page, 3000)


async def checks(page: Page, base: str) -> None:
    await page.goto(base + "checks")
    await settle(page, 2600)


VIEWS = {"follow": follow, "tick": tick, "card": card, "compare": compare, "checks": checks}


def webp(png: Path, out: Path, width: int) -> None:
    subprocess.run(["cwebp", "-quiet", "-q", "80", "-resize", str(width), "0", str(png), "-o", str(out)], check=True)


async def main(base: str, only: list[str]) -> None:
    base = base if base.endswith("/") else base + "/"
    OUT.mkdir(parents=True, exist_ok=True)
    async with async_playwright() as p:
        browser = await p.chromium.launch()
        for scheme in ("light", "dark"):
            context = await browser.new_context(viewport={"width": WIDTH, "height": HEIGHT}, device_scale_factor=2, color_scheme=scheme)
            for name, go in VIEWS.items():
                if only and name not in only:
                    continue
                page = await context.new_page()
                await go(page, base)
                with tempfile.TemporaryDirectory() as tmp:
                    png = Path(tmp) / "shot.png"
                    await page.screenshot(path=str(png))
                    for width in (1440, 2880):
                        webp(png, OUT / f"tour-{name}-{scheme}-{width}.webp", width)
                print(f"tour-{name}-{scheme}: {page.url}")
                await page.close()
            await context.close()
        await browser.close()


if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    asyncio.run(main(sys.argv[1], sys.argv[2:]))
