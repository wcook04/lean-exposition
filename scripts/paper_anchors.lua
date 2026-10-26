-- Keep the manuscripts' HTML bookmarks when Pandoc writes LaTeX.
-- Pandoc drops raw HTML and empty Divs in LaTeX. Preserve the existing IDs
-- as hyperref labels, with a fresh destination at the original text position.
function RawBlock(block)
  if FORMAT == "latex" and block.format == "html" then
    if block.text:match('^%s*<!%-%- pdf%-page%-break %-%->%s*$') then
      return pandoc.RawBlock("latex", "\\newpage")
    end
    local id = block.text:match('^%s*<a%s+id="([%w_:%.%-]+)"%s*>%s*</a>%s*$')
    if id then
      return pandoc.RawBlock("latex", "\\hypertarget{" .. id .. "}{}\\phantomsection\\label{" .. id .. "}")
    end
  end
end

function RawInline(inline)
  if FORMAT == "latex" and inline.format == "html" then
    local id = inline.text:match('^<a%s+id="([%w_:%.%-]+)"%s*>$')
    if id then
      return pandoc.RawInline("latex", "\\hypertarget{" .. id .. "}{}\\phantomsection\\label{" .. id .. "}")
    end
  end
end

-- A standalone PDF cannot promise that neighbouring repository files travel
-- with it. Opt in per manuscript: keep descriptive local-link text, while
-- preserving internal destinations and public URLs. HTML/Markdown are unchanged.
function Pandoc(doc)
  if FORMAT ~= "latex" then
    return doc
  end
  local portable = doc.meta["portable-local-links"] == true
  return doc:walk({Span = function(span)
    if not span.classes:includes("pdf-companion") then
      return span
    end
    local target = span.attributes["data-pdf-target"]
    local anchor = span.attributes["data-pdf-anchor"]
    if portable or not target then
      return span.content
    end
    if anchor then
      target = target .. "#" .. anchor
    end
    -- Keep the ordinary Markdown destination in HTML, but replace it without
    -- nesting links when producing the matching PDF reading edition.
    local label = pandoc.Span(span.content):walk({Link = function(link)
      return link.content
    end}).content
    return pandoc.Link(label, target)
  end, Link = function(link)
    local target = link.target
    if target:match("^#") or target:match("^https?://") or target:match("^mailto:") then
      return link
    end
    if portable then
      return link.content
    end
    -- Browsers use #nameddest=ID; hyperref's local PDF links expect #ID
    -- and otherwise look for the literal destination "nameddest=ID".
    local file, id = target:match("^(.-%.pdf)#nameddest=([%w_:%.%-]+)$")
    if file then
      link.target = file .. "#" .. id
    end
    return link
  end})
end
