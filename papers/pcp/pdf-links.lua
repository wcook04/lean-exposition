-- Adapt the existing paper_anchors.lua companion policy for this paper family.
-- Reading packets preserve the three stage directories and their PDF names.
function Pandoc(doc)
  if FORMAT ~= "latex" or doc.meta["keep-display-leads"] ~= true then return doc end
  return doc:walk({Blocks = function(blocks)
    local result = pandoc.List()
    for i, block in ipairs(blocks) do
      result:insert(block)
      local next_block = blocks[i + 1]
      if block.t == "Para" and next_block and next_block.t == "Para"
        and #next_block.content == 1 and next_block.content[1].t == "Math"
        and next_block.content[1].mathtype == "DisplayMath"
        and not (#block.content == 1 and block.content[1].t == "Math") then
        result:insert(pandoc.RawBlock("latex", "\\nopagebreak[4]"))
      end
    end
    return result
  end})
end

function Header(header)
  if FORMAT == "latex" and header.identifier ~= "" then
    -- Hyperref's section destination can have an internal name unrelated to
    -- the Markdown heading. Export the same explicit destination used by
    -- paper_anchors.lua for HTML bookmarks so companion links can target it.
    return {pandoc.RawBlock("latex", "\\hypertarget{" .. header.identifier .. "}{}"), header}
  end
  return header
end

function Table(tbl)
  if FORMAT ~= "latex" then return tbl end
  local rows = 0
  for _, body in ipairs(tbl.bodies) do rows = rows + #body.body end
  if rows <= 4 then
    -- Reserve space for a compact comparison, including wrapped cell text.
    return {pandoc.RawBlock("latex", "\\Needspace{" .. (3 * rows + 2) .. "\\baselineskip}"), tbl}
  end
  return tbl
end

function Link(link)
  if FORMAT ~= "latex" then return link end
  local file, fragment = link.target:match("^(%.%./[^#]+%.md)(.*)$")
  local companions = {
    ["../long/reasoning-record.md"] = "../long/reasoning-record.pdf",
    ["../short/paper.md"] = "../short/paper.pdf",
    ["../expository/main.md"] = "../expository/main.pdf",
  }
  if file and companions[file] then
    link.target = companions[file] .. fragment
  end
  return link
end
