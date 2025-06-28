local fmt = string.format


local function makeitem(info)
  return pandoc.List {
    pandoc.Plain { -- This is a <li>
      pandoc.Link ({
        pandoc.Span(info.title, {class = "title"}),
        pandoc.Span(info.year, {class = "date"}),
      }, info.href)
    }
  }
end


paperlist = pandoc.BulletList({
  makeitem({title="Relational Graphical Linear Algebra (Bachelor's Dissertation)",year="2023",href="/pdfs/relational_graphical_linear_algebra.pdf"}),
  makeitem({title="Explicit Computation on Elliptic Curves (Master's Dissertation)",year="2025",href="/pdfs/explicit_computation_on_elliptic_curves.pdf"})
})


function Block(elem)
  if elem.content then
    local text = pandoc.utils.stringify(elem.content)
    local num = string.match(text, "^%s*{{%s*paper%-list%s*(%d*)%s*}}%s*$")
    if num then
      return pandoc.Div({paperlist}, {class = "post-list"})
    end
  end
end
