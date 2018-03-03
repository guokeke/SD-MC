</
  define p: input$=6;
  define q: output$=22;
  define r: output$=26;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>