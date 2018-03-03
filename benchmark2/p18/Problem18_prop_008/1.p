</
  define p: input$=1;
  define q: output$=21;
  define r: output$=22;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>
