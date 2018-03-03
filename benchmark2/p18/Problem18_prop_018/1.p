</
  define p: output$=22;
  define q: input$=3;
  define r: output$=21;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>