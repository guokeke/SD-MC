</
  define p: input$=5;
  define q: input$=6;
  define r: output$=23;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>