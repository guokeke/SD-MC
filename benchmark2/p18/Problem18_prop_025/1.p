</
  define p: input$=6;
  define q: output$=26;
  define r: output$=24;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>
