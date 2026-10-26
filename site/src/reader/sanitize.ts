// HTML sanitisation for rendered Markdown (before KaTeX output is substituted).
//
// Only the elements and attributes the manuscripts need survive. `style` is
// kept only as table-cell alignment; hrefs are restricted to in-document
// fragments, the reader's own `/read/` routes, http(s) and mailto.

import createDOMPurify, { type DOMPurify } from "dompurify";

const ALLOWED_TAGS = [
  "h1", "h2", "h3", "h4", "h5", "h6", "p", "a", "em", "strong", "code", "pre",
  "ul", "ol", "li", "table", "thead", "tbody", "tr", "th", "td", "blockquote",
  "hr", "br", "span", "figure", "figcaption", "div", "sup", "sub", "del", "s",
];

const ALLOWED_ATTR = ["href", "id", "class", "title", "target", "rel", "style", "start", "aria-hidden"];

const ALIGN = /^\s*text-align\s*:\s*(left|right|center)\s*;?\s*$/i;
const SAFE_HREF = /^(#|\/read\/|https?:\/\/|mailto:)/i;

let instance: DOMPurify | null = null;

function purifier(): DOMPurify {
  if (instance) return instance;
  if (typeof window === "undefined") throw new Error("sanitize: a DOM window is required");
  const p = createDOMPurify(window);
  p.addHook("uponSanitizeAttribute", (node, data) => {
    const tag = node.nodeName.toLowerCase();
    if (data.attrName === "style") {
      data.keepAttr = (tag === "td" || tag === "th") && ALIGN.test(data.attrValue);
    } else if (data.attrName === "href") {
      data.keepAttr = tag === "a" && SAFE_HREF.test(data.attrValue.trim());
    } else if (data.attrName === "target") {
      data.keepAttr = tag === "a" && data.attrValue === "_blank";
    }
  });
  p.addHook("afterSanitizeAttributes", (node) => {
    if (node.nodeName.toLowerCase() === "a" && node.getAttribute("target") === "_blank") {
      node.setAttribute("rel", "noopener noreferrer");
    }
  });
  instance = p;
  return p;
}

export function sanitizeHtml(html: string): string {
  return purifier().sanitize(html, {
    ALLOWED_TAGS,
    ALLOWED_ATTR,
    ALLOW_DATA_ATTR: true,
    ALLOW_ARIA_ATTR: false,
    KEEP_CONTENT: true,
    RETURN_TRUSTED_TYPE: false,
  }) as string;
}
