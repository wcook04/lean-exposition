-- Keep the manuscripts' HTML bookmarks when Pandoc writes LaTeX.
-- Pandoc drops raw HTML and empty Divs in LaTeX. Preserve the existing IDs
-- as hyperref labels, with a fresh destination at the original text position.
function RawBlock(block)
  if FORMAT == "latex" and block.format == "html" then
    local id = block.text:match('^%s*<a%s+id="([%w_:%.%-]+)"%s*>%s*</a>%s*$')
    if id then
      return pandoc.RawBlock("latex", "\\phantomsection\\label{" .. id .. "}")
    end
  end
end

function RawInline(inline)
  if FORMAT == "latex" and inline.format == "html" then
    local id = inline.text:match('^<a%s+id="([%w_:%.%-]+)"%s*>$')
    if id then
      return pandoc.RawInline("latex", "\\phantomsection\\label{" .. id .. "}")
    end
  end
end

-- A standalone PDF cannot promise that neighbouring repository files travel
-- with it. Opt in per manuscript: keep descriptive local-link text, while
-- preserving internal destinations and public URLs. HTML/Markdown are unchanged.
function Pandoc(doc)
  if FORMAT ~= "latex" or doc.meta["portable-local-links"] ~= true then
    return doc
  end
  return doc:walk({Link = function(link)
    local target = link.target
    if target:match("^#") or target:match("^https?://") or target:match("^mailto:") then
      return link
    end
    return link.content
  end})
end
