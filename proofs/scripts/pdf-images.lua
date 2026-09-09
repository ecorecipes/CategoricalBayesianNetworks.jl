function Image(image)
  if FORMAT:match("latex") then
    image.src = image.src:gsub("%.svg$", ".pdf")
  end
  return image
end
