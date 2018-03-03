</
  define p: input$=5;
  define q: input$=2;
  define r: output$=22;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>