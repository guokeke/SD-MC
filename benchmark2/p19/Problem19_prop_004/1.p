</
  define p: output$=22;
  define q: input$=2;
  define r: output$=23;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>
