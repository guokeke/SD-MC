</
  define p: input$=6;
  define q: input$=3;
  define r: output$=21;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>
