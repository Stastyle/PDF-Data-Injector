import tkinter as tk
from tkinter import filedialog, messagebox, font as tkFont, simpledialog, ttk
import pandas as pd
import fitz  # PyMuPDF
import os
import arabic_reshaper
from bidi.algorithm import get_display
import matplotlib.font_manager as fm # Added for finding font file paths

# Define marker colors for dynamic text fields
MARKER_COLORS = ["red", "blue", "green", "purple", "orange", "cyan", "magenta", "brown", "pink", "olive"]

# Class constants
Y_OFFSET_PDF_OUTPUT = 2  # Small Y offset adjustment for PDF output, in points
TKINTER_FONT_SCALE_FACTOR = 0.85 # Adjust this factor as needed for Tkinter's font rendering vs PDF
DEFAULT_PDF_TEXT_COLOR = (0, 0, 0) # Black

class PDFBatchApp:
    def __init__(self, master):
        self.master = master
        master.title("PDF Data Injector")
        master.geometry("950x800") # Increased height for preview

        # --- Variables ---
        self.pdf_path = tk.StringVar()
        self.excel_path = tk.StringVar()
        self.output_dir = tk.StringVar()
        # StringVars for displaying only filenames/directory names
        self.pdf_display_var = tk.StringVar(value="(No file selected)")
        self.excel_display_var = tk.StringVar(value="(No file selected)")
        self.output_dir_display_var = tk.StringVar(value="(No folder selected)")
        self.font_family_var = tk.StringVar() 
        self.font_size_var = tk.IntVar(value=12)     # Default font size
        self.excel_preview_text = tk.StringVar(value="Excel Preview: (Load Excel file)") # For internal data, not displayed directly
        self.current_zoom_factor = tk.DoubleVar(value=1.0)
        self.zoom_display_var = tk.StringVar(value="זום: 100%")
        self.preview_row_index = tk.IntVar(value=0) # 0-based index for preview row
        self.preview_row_display = tk.StringVar(value="שורה: -")
        
        self.is_rtl_vars = [] # List of tk.BooleanVar for RTL status of each column
        self.col_status_vars = [] # List of tk.StringVar for V/X status of each column

        self._bind_font_variables()

        self.pdf_doc = None
        self.pdf_page_width_pt = 0
        self.pdf_page_height_pt = 0
        self.image_on_canvas_width_px = 0
        self.image_on_canvas_height_px = 0

        self.photo_image = None # To prevent garbage collection
        self.coords_pdf = [] # List to store PDF coordinates for each text field
        self.active_coord_to_set_idx = None # Index of the coordinate currently being set by click
        self.excel_data_preview = None
        self.num_excel_cols = 0 # Number of columns detected in Excel, determines number of text fields
        self.preview_text_items = [] # Store IDs of preview text items on canvas
        self.is_text_preview_active = True # Default to text preview being active
        self._drag_data = {"x": 0, "y": 0, "item": None, "col_idx": None} # For dragging markers
        # self._pan_data = {"x": 0, "y": 0, "active": False} # Old, for Button-3 panning
        self._pan_data = {
            "press_x": 0, "press_y": 0,  # Coords of initial B1 press on canvas
            "is_potential_pan_or_click": False,  # True after B1 press on canvas (not on marker)
            "has_dragged_for_pan": False,  # True if mouse moved enough during B1 hold
            "pan_threshold": 5  # pixels, adjust as needed
        }

        # --- GUI Layout ---
        # Main application frame
        main_app_frame = tk.Frame(master)
        main_app_frame.pack(fill=tk.BOTH, expand=True)

        # Frame for file selection and controls
        controls_frame = tk.Frame(main_app_frame, padx=10, pady=10)
        controls_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)

        # Content area for canvas and sidebar
        content_area_frame = tk.Frame(main_app_frame)
        content_area_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=5, pady=(0,5))

        # PDF Selection
        tk.Label(controls_frame, text="PDF Template:").grid(row=0, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select PDF", command=self.load_pdf_template, width=12).grid(row=0, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.pdf_display_var, width=40, state="readonly").grid(row=0, column=2, padx=5, pady=2, sticky="ew")

        # Excel Selection
        tk.Label(controls_frame, text="Excel Data File:").grid(row=1, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select Excel", command=self.load_excel_data, width=12).grid(row=1, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.excel_display_var, width=40, state="readonly").grid(row=1, column=2, padx=5, pady=2, sticky="ew")

        # Output Directory Selection
        tk.Label(controls_frame, text="Output Folder:").grid(row=2, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select Folder", command=self.select_output_dir, width=12).grid(row=2, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.output_dir_display_var, width=40, state="readonly").grid(row=2, column=2, padx=5, pady=2, sticky="ew")

        # Font Selection
        tk.Label(controls_frame, text="Font Family:").grid(row=3, column=0, sticky="e", padx=5, pady=2)
        font_details_frame = tk.Frame(controls_frame)
        font_details_frame.grid(row=3, column=1, columnspan=2, sticky="e", padx=5, pady=2) 
        
        # Populate font families
        font_families = sorted(list(tkFont.families()))
        self.font_combo = ttk.Combobox(font_details_frame, textvariable=self.font_family_var, values=font_families, width=23, state="readonly")
        if "Arial" in font_families:
            self.font_family_var.set("Arial") # Default font
        elif font_families:
            self.font_family_var.set(font_families[0]) # Fallback to first available font
        self.font_combo.pack(side=tk.LEFT)

        tk.Label(font_details_frame, text="Size:").pack(side=tk.LEFT, padx=(10, 2))
        tk.Entry(font_details_frame, textvariable=self.font_size_var, width=5).pack(side=tk.LEFT)

        # Zoom controls and Text Preview Button
        zoom_preview_frame = tk.Frame(controls_frame)
        zoom_preview_frame.grid(row=4, column=0, columnspan=3, sticky="e", pady=5) # Adjusted row
        tk.Button(zoom_preview_frame, text="-", command=lambda: self.zoom(-0.2)).pack(side=tk.LEFT, padx=2)
        tk.Label(zoom_preview_frame, textvariable=self.zoom_display_var).pack(side=tk.LEFT, padx=5)
        tk.Button(zoom_preview_frame, text="+", command=lambda: self.zoom(0.2)).pack(side=tk.LEFT, padx=2)
        
        # Preview Row Controls
        self.prev_row_button = tk.Button(zoom_preview_frame, text="↑", command=lambda: self._change_preview_row(-1), state=tk.DISABLED, width=2)
        self.prev_row_button.pack(side=tk.LEFT, padx=(15,0)) 

        self.preview_row_label = tk.Label(zoom_preview_frame, textvariable=self.preview_row_display, width=8)
        self.preview_row_label.pack(side=tk.LEFT, padx=2)

        self.next_row_button = tk.Button(zoom_preview_frame, text="↓", command=lambda: self._change_preview_row(1), state=tk.DISABLED, width=2)
        self.next_row_button.pack(side=tk.LEFT, padx=(0,5))

        tk.Button(zoom_preview_frame, text="Show/Hide Preview", command=self.toggle_text_preview).pack(side=tk.LEFT, padx=(10,0))
        # "Generate current PDF" button moved below

        # Generate Buttons Frame (for main generate and current generate)
        generate_buttons_frame = tk.Frame(controls_frame)
        generate_buttons_frame.grid(row=5, column=0, columnspan=3, sticky="e", pady=10)

        self.generate_all_pdfs_button = tk.Button(generate_buttons_frame, text="Generate PDF Files", command=self.generate_output_pdfs, bg="lightblue", font=("Arial", 12, "bold"))
        self.generate_all_pdfs_button.pack(side=tk.RIGHT, padx=(5,0)) 

        self.generate_current_pdf_button = tk.Button(generate_buttons_frame, text="Generate current PDF", command=self.generate_single_preview_pdf)
        self.generate_current_pdf_button.pack(side=tk.RIGHT)

        # Status Label
        self.status_label = tk.Label(main_app_frame, text="Please load a PDF template to begin.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)

        # Canvas for PDF Preview
        self.canvas_container = tk.Frame(content_area_frame, bd=2, relief=tk.SUNKEN)
        self.canvas_container.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))

        # Sidebar for dynamic column controls
        self.column_controls_sidebar = tk.Frame(content_area_frame, width=200, bd=1, relief=tk.RAISED)
        self.column_controls_sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=(5,0))
        self.canvas = tk.Canvas(self.canvas_container, bg="lightgrey") # Changed bg for better visibility

        self.h_scrollbar = tk.Scrollbar(self.canvas_container, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.v_scrollbar = tk.Scrollbar(self.canvas_container, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)

        self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # self.canvas.bind("<Button-1>", self.handle_canvas_click) # Replaced by specific B1 bindings
        self.canvas.bind("<ButtonPress-1>", self._on_canvas_b1_press)
        self.canvas.bind("<B1-Motion>", self._on_canvas_b1_motion)
        self.canvas.bind("<ButtonRelease-1>", self._on_canvas_b1_release)

        # Bindings for dragging markers
        self.canvas.tag_bind("marker", "<ButtonPress-1>", self.on_marker_press)
        self.canvas.tag_bind("marker", "<B1-Motion>", self.on_marker_motion)
        self.canvas.tag_bind("marker", "<ButtonRelease-1>", self.on_marker_release)
        self.canvas.tag_bind("marker", "<Double-Button-1>", self.on_marker_double_click)

        # Bindings for mouse wheel zoom
        self.canvas.bind("<MouseWheel>", self._handle_mouse_wheel_zoom)  # Windows & MacOS
        self.canvas.bind("<Button-4>", self._handle_mouse_wheel_zoom)    # Linux scroll up
        self.canvas.bind("<Button-5>", self._handle_mouse_wheel_zoom)    # Linux scroll down


    def _bind_font_variables(self):
        self.font_family_var.trace_add("write", self._on_font_change)
        self.font_size_var.trace_add("write", self._on_font_change)
        # RTL vars are bound dynamically in _build_dynamic_coord_controls

    def _on_font_change(self, *args):
        if self.is_text_preview_active:
            self._update_text_preview()

    def _build_dynamic_coord_controls(self):
        # Clear existing controls
        for widget in self.column_controls_sidebar.winfo_children():
            widget.destroy()
        
        self.is_rtl_vars = []
        self.col_status_vars = []
        # self.coords_pdf is already initialized in load_excel_data

        if self.num_excel_cols == 0:
            tk.Label(self.column_controls_sidebar, text="Load Excel file\nto define text fields.", justify=tk.CENTER).pack(pady=20)
            return

        for i in range(self.num_excel_cols):
            rtl_var = tk.BooleanVar(value=True)
            rtl_var.trace_add("write", self._on_font_change)
            self.is_rtl_vars.append(rtl_var)

            status_var = tk.StringVar(value="✖") # Default to not placed
            self.col_status_vars.append(status_var)

            item_frame = tk.Frame(self.column_controls_sidebar, bd=1, relief=tk.SOLID) # Frame for each item's controls
            item_frame.pack(fill=tk.X, padx=5, pady=3)

            status_label_text = f"Col {i+1}:" # Shorter label
            
            # Status indicator (V/X) and Column Label
            tk.Label(item_frame, textvariable=status_var, width=2, font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(2,0))
            tk.Label(item_frame, text=status_label_text).pack(side=tk.LEFT, padx=(0,5))
            
            ttk.Checkbutton(item_frame, text="RTL", variable=rtl_var, width=5).pack(side=tk.LEFT, padx=(0,5))
            tk.Button(item_frame, text="Move", command=lambda idx=i: self.prepare_to_set_coord(idx)).pack(side=tk.LEFT, padx=5)

    def prepare_to_set_coord(self, col_idx):
        if self.pdf_doc:
            self.active_coord_to_set_idx = col_idx
            self.status_label.config(text=f"Select position for column {col_idx + 1} on the image, or drag the marker.")
            self._drag_data["item"] = None
            # If text preview is active, update it to potentially clear old highlights or focus
            if self.is_text_preview_active:
                self._update_text_preview()
        else:
            self.status_label.config(text="Please load a PDF file first.")

    def _change_preview_row(self, direction):
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            return

        current_idx = self.preview_row_index.get()
        new_idx = current_idx + direction
        num_rows = self.excel_data_preview.shape[0]

        if 0 <= new_idx < num_rows:
            self.preview_row_index.set(new_idx)
            self._update_preview_row_display_and_buttons()
            if self.is_text_preview_active:
                self._update_text_preview()

    def _update_preview_row_display_and_buttons(self):
        if self.excel_data_preview is not None and not self.excel_data_preview.empty:
            current_idx = self.preview_row_index.get()
            num_rows = self.excel_data_preview.shape[0]
            self.preview_row_display.set(f"Row: {current_idx + 1}")

            self.prev_row_button.config(state=tk.NORMAL if current_idx > 0 else tk.DISABLED)
            self.next_row_button.config(state=tk.NORMAL if current_idx < num_rows - 1 else tk.DISABLED)
        else:
            self.preview_row_display.set("Row: -")
            self.prev_row_button.config(state=tk.DISABLED)
            self.next_row_button.config(state=tk.DISABLED)

    def _handle_mouse_wheel_zoom(self, event):
        if not self.pdf_doc:
            return

        factor_change = 0
        # Respond to Linux wheel events
        if event.num == 4: # Scroll up
            factor_change = 0.1
        elif event.num == 5: # Scroll down
            factor_change = -0.1
        # Respond to Windows/Mac wheel events
        elif event.delta > 0: # Scroll up
            factor_change = 0.1
        elif event.delta < 0: # Scroll down
            factor_change = -0.1
        
        if factor_change != 0:
            self.zoom(factor_change)

    def zoom(self, factor_change):
        if not self.pdf_doc:
            return
        new_zoom = self.current_zoom_factor.get() + factor_change # Min 20%, Max 500% zoom
        if 0.2 <= new_zoom <= 5.0: 
            self.current_zoom_factor.set(round(new_zoom, 2))
            self.zoom_display_var.set(f"Zoom: {int(self.current_zoom_factor.get() * 100)}%")
            self._redisplay_pdf_page()

    def _redisplay_pdf_page(self):
        if not self.pdf_doc:
            return

        page = self.pdf_doc.load_page(0)
        zoom_val = self.current_zoom_factor.get()
        mat = fitz.Matrix(zoom_val, zoom_val)
        pix = page.get_pixmap(matrix=mat)

        self.image_on_canvas_width_px = pix.width
        self.image_on_canvas_height_px = pix.height

        self.photo_image = tk.PhotoImage(data=pix.tobytes("ppm"))

        self.canvas.delete("pdf_image") # Delete only the old PDF image
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image, tags="pdf_image")
        self.canvas.config(scrollregion=(0, 0, self.image_on_canvas_width_px, self.image_on_canvas_height_px))

        self._draw_markers()
        if self.is_text_preview_active:
            self._update_text_preview()

    def _draw_markers(self):
        self.canvas.delete("marker") # Delete all items with the general "marker" tag
        marker_radius = 5
        for i, pdf_coord in enumerate(self.coords_pdf):
            if pdf_coord:
                canvas_coords = self._pdf_coords_to_canvas_coords(pdf_coord)
                if canvas_coords:
                    color = MARKER_COLORS[i % len(MARKER_COLORS)]
                    marker_tag = f"marker_{i}" # Unique tag for each marker based on index
                    self.canvas.create_rectangle(canvas_coords[0] - marker_radius, canvas_coords[1] - marker_radius,
                                                 canvas_coords[0] + marker_radius, canvas_coords[1] + marker_radius,
                                                 fill=color, outline=color, tags=(marker_tag, "marker")) # Add general "marker" tag too

    def _pdf_coords_to_canvas_coords(self, pdf_coords_tuple):
        if not self.pdf_doc or self.pdf_page_width_pt == 0 or self.pdf_page_height_pt == 0:
            return None
        pdf_x_pt, pdf_y_pt_from_bottom = pdf_coords_tuple

        # Convert PDF coordinates (origin bottom-left) to canvas image coordinates (origin top-left)
        canvas_x_on_image = (pdf_x_pt / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        
        # PDF Y is from bottom, Canvas Y is from top.
        # So, (1 - (pdf_y / pdf_height)) gives the proportional distance from the top of the PDF.
        canvas_y_on_image = (1 - (pdf_y_pt_from_bottom / self.pdf_page_height_pt)) * self.image_on_canvas_height_px

        return (canvas_x_on_image, canvas_y_on_image)

    def load_pdf_template(self):
        path = filedialog.askopenfilename(
            title="Select PDF File",
            filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )
        if not path:
            return

        self.pdf_path.set(path)
        self.pdf_display_var.set(os.path.basename(path) if path else "(No file selected)")
        try:
            self.pdf_doc = fitz.open(path)
            if not self.pdf_doc.page_count > 0:
                messagebox.showerror("שגיאה", "קובץ ה-PDF ריק.")
                self.pdf_doc = None
                return

            page = self.pdf_doc.load_page(0) # Load first page
            self.pdf_page_width_pt = page.rect.width
            self.pdf_page_height_pt = page.rect.height

            self.current_zoom_factor.set(1.0) # Reset zoom
            self.zoom_display_var.set(f"Zoom: 100%")
            # Calculate initial zoom to fit page (optional, or start at 100%)
            # For simplicity, we start at 100% and user can zoom.
            # If you want fit-to-page initially:
            # self.master.update_idletasks()
            # canvas_width_initial = self.canvas.winfo_width()
            # canvas_height_initial = self.canvas.winfo_height()
            # zoom_x_initial = canvas_width_initial / self.pdf_page_width_pt
            # zoom_y_initial = canvas_height_initial / self.pdf_page_height_pt
            # self.current_zoom_factor.set(min(zoom_x_initial, zoom_y_initial, 1.0)) # Fit or 100%

            self._redisplay_pdf_page()
            
            if self.num_excel_cols > 0:
                self.status_label.config(text=f"PDF file loaded. Click 'Move' next to a column to position it, or click on the image for chronological placement.")
                if self.is_text_preview_active and any(c is not None for c in self.coords_pdf): # Check if any coord is set
                    self._update_text_preview()
            else:
                self.status_label.config(text="PDF file loaded. Load an Excel file to define text fields.")
            
            # No specific column is being set by "Move" button initially
            # self.active_coord_to_set_idx = None # This is already the default
            self._update_text_preview() # Will clear if coords are None

        except Exception as e:
            messagebox.showerror("Error Loading PDF", str(e))
            self.pdf_doc = None
            self.pdf_display_var.set("(Error loading)")
            self.pdf_path.set("")


    def load_excel_data(self):
        path = filedialog.askopenfilename(
            title="Select Excel File",
            filetypes=(("Excel files", "*.xlsx *.xls"), ("All files", "*.*"))
        )
        if not path:
            return
        self.excel_path.set(path)
        self.excel_display_var.set(os.path.basename(path) if path else "(No file selected)")
        try:
            df = pd.read_excel(path, header=None) # Assume no header for simplicity, take first two columns
            if df.empty or df.shape[1] == 0:
                messagebox.showerror("שגיאה", "קובץ האקסל ריק או אינו מכיל עמודות.")
                self.excel_path.set("")
                self.num_excel_cols = 0
                self.excel_display_var.set("(Empty or invalid file)")
                self.coords_pdf = []
                return
            
            self.num_excel_cols = df.shape[1]
            self.coords_pdf = [None] * self.num_excel_cols # Initialize/reset coords list
            # Initialize status vars when Excel is loaded
            self.col_status_vars = [tk.StringVar(value="✖") for _ in range(self.num_excel_cols)]
            self._build_dynamic_coord_controls() # Rebuild UI for coordinates
            
            # Improved Excel Preview
            preview_text_summary = "Excel Preview Summary:\n" # For internal data, not displayed directly
            if not df.empty:
                # Preview first row
                if df.shape[1] >= 1: # Check if there's at least one column
                    val1_r1 = str(df.iloc[0, 0]) if pd.notna(df.iloc[0, 0]) else ""
                    preview_text_summary += f"Row 1: Col 1 = {val1_r1}"
                    if self.num_excel_cols >= 2: # Check if there's a second column
                        val2_r1 = str(df.iloc[0, 1]) if pd.notna(df.iloc[0,1]) else ""
                        preview_text_summary += f", Col 2 = {val2_r1 if self.num_excel_cols > 1 else ''}"
                else:
                    preview_text_summary += "Row 1: (No data columns)"

                # Preview second row if it exists
                if df.shape[0] > 1: # Check if there's a second row
                    preview_text_summary += "\n"
                    if df.shape[1] >= 1:
                        val1_r2 = str(df.iloc[1, 0]) if pd.notna(df.iloc[1, 0]) else ""
                        preview_text_summary += f"Row 2: Col 1 = {val1_r2}"
                        if self.num_excel_cols >= 2:
                            val2_r2 = str(df.iloc[1, 1]) if pd.notna(df.iloc[1,1]) else ""
                            preview_text_summary += f", Col 2 = {val2_r2 if self.num_excel_cols > 1 else ''}"
            else:
                preview_text_summary += "Excel file is empty."
            self.excel_preview_text.set(preview_text_summary) # Store summary, not directly displayed as a label anymore
            if self.pdf_doc:
                 self.status_label.config(text=f"Excel loaded ({self.num_excel_cols} cols). Click on image to position Col 1, or use 'Move'.")
            else:
                 self.status_label.config(text=f"Excel loaded ({self.num_excel_cols} cols). Load PDF to start positioning.")
            self.excel_data_preview = df
            self.preview_row_index.set(0) # Reset to first row for preview
            self._update_preview_row_display_and_buttons() # Update buttons AFTER df is set
            # Try to update preview if PDF is also loaded and at least one coord is set
            if self.is_text_preview_active and self.pdf_doc and any(c is not None for c in self.coords_pdf):
                self._update_text_preview()
        except Exception as e:
            messagebox.showerror("Error Loading Excel", str(e))
            self.excel_path.set("")
            self.excel_display_var.set("(Error loading)")
            self.excel_preview_text.set("Excel Preview: (Error loading)")
            self.num_excel_cols = 0
            self.preview_row_index.set(0)
            self._update_preview_row_display_and_buttons()
            self._build_dynamic_coord_controls()
            self.excel_data_preview = None

    def select_output_dir(self):
        path = filedialog.askdirectory(title="Select Output Folder")
        if not path:
            return
        self.output_dir.set(path)
        self.output_dir_display_var.set(os.path.basename(path) if path else "(No folder selected)")
        self.status_label.config(text=f"Output folder selected: {path}")
    def _canvas_coords_to_pdf_coords(self, canvas_x, canvas_y):
        """Converts canvas click coordinates to PDF points (bottom-left origin)."""
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        prop_x = canvas_x / self.image_on_canvas_width_px
        prop_y = canvas_y / self.image_on_canvas_height_px

        pdf_x_pt = prop_x * self.pdf_page_width_pt # Use original PDF width for calculation
        pdf_y_pt_from_top = prop_y * self.pdf_page_height_pt # Use original PDF height
        pdf_y_pt_from_bottom = self.pdf_page_height_pt - pdf_y_pt_from_top

        return (pdf_x_pt, pdf_y_pt_from_bottom)

    def _on_canvas_b1_press(self, event):
        # Check if the click is on an existing marker.
        # The marker's own tag binding (on_marker_press) will handle the drag initiation.
        current_item_tuple = self.canvas.find_withtag(tk.CURRENT)
        if current_item_tuple:
            item_id = current_item_tuple[0]
            if "marker" in self.canvas.gettags(item_id):
                # Let on_marker_press (already bound to the marker tag) handle this.
                # on_marker_press will set self._drag_data["item"].
                return

        # If not on a marker, this B1 press could be the start of a pan or a click-to-place.
        if not self.pdf_doc:
            self.status_label.config(text="Please load a PDF file first.")
            return

        # Store press coordinates and prepare for potential pan
        self._pan_data["press_x"] = self.canvas.canvasx(event.x) # Use canvas coords
        self._pan_data["press_y"] = self.canvas.canvasy(event.y) # Use canvas coords
        self._pan_data["is_potential_pan_or_click"] = True
        self._pan_data["has_dragged_for_pan"] = False
        self.canvas.scan_mark(event.x, event.y) # For scan_dragto, event.x/y is fine

    def _on_canvas_b1_motion(self, event):
        if self._drag_data["item"]:
            # A marker is being dragged by its own bindings (on_marker_motion), so do nothing here.
            return

        if self._pan_data["is_potential_pan_or_click"]:
            if not self._pan_data["has_dragged_for_pan"]: # Check only once if it becomes a drag
                # Check if movement exceeds threshold for panning
                # Use canvas coordinates for calculating drag distance
                current_canvas_x = self.canvas.canvasx(event.x)
                current_canvas_y = self.canvas.canvasy(event.y)
                dx = abs(current_canvas_x - self._pan_data["press_x"])
                dy = abs(current_canvas_y - self._pan_data["press_y"])

                if dx > self._pan_data["pan_threshold"] or dy > self._pan_data["pan_threshold"]:
                    self._pan_data["has_dragged_for_pan"] = True
            
            if self._pan_data["has_dragged_for_pan"]:
                if self.pdf_doc: # Ensure PDF is loaded before trying to pan
                    self.canvas.config(cursor="fleur")
                    self.canvas.scan_dragto(event.x, event.y, gain=1) # event.x/y is fine for scan_dragto

    def _on_canvas_b1_release(self, event):
        # If a marker drag was just completed, self._drag_data["item"] would have been cleared by on_marker_release.
        # We primarily care about actions initiated by _on_canvas_b1_press here.

        if self._pan_data["is_potential_pan_or_click"]:
            if self._pan_data["has_dragged_for_pan"]:
                # Pan occurred
                self.canvas.config(cursor="") # Reset cursor from "fleur"
            else:
                # No significant drag, so it's a click-to-place action.
                # Ensure that a marker drag didn't *just* happen and clear _drag_data["item"]
                # If _drag_data["item"] is None now, it means either no marker drag started,
                # or a marker drag finished. We only want to place if no marker drag was involved.
                # The check in _on_canvas_b1_press (find_withtag) should prevent this path if a marker was initially clicked.
                if not self._drag_data["item"]: # Double check no marker drag is active
                     self._execute_place_marker_at_click(event)

            # Reset pan_data for the next B1 interaction on the canvas
            self._pan_data["is_potential_pan_or_click"] = False
            self._pan_data["has_dragged_for_pan"] = False

    def _execute_place_marker_at_click(self, event):
        if not self.pdf_doc: # This check is good to have here too
            return

        idx_to_update = -1

        if self.active_coord_to_set_idx is not None: # User clicked "Move" button for a specific column
            idx_to_update = self.active_coord_to_set_idx
        else: # No specific column chosen, try to find the next unassigned one
            if self.num_excel_cols > 0 and self.coords_pdf:
                try:
                    idx_to_update = self.coords_pdf.index(None) # Find first unassigned coordinate
                except ValueError: # All coordinates are assigned
                    self.status_label.config(text="All columns positioned. Use 'Move' button or drag markers to change.")
                    return
            else: # No Excel loaded or no columns
                self.status_label.config(text="Load Excel file to define columns for positioning.")
                return

        if idx_to_update != -1:
            # Convert event coordinates to canvas coordinates (accounts for scrolling)
            canvas_x = self.canvas.canvasx(event.x)
            canvas_y = self.canvas.canvasy(event.y)

            if not (0 <= canvas_x <= self.image_on_canvas_width_px and \
                    0 <= canvas_y <= self.image_on_canvas_height_px):
                self.status_label.config(text="Click within the image boundaries.")
                return

            pdf_coords = self._canvas_coords_to_pdf_coords(canvas_x, canvas_y)
            if not pdf_coords:
                self.status_label.config(text="Error calculating coordinates.")
                return

            self.coords_pdf[idx_to_update] = pdf_coords
            if idx_to_update < len(self.col_status_vars):
                self.col_status_vars[idx_to_update].set("✔")
            
            # Check if there's a next unassigned coordinate
            next_unassigned_idx = -1
            try:
                next_unassigned_idx = self.coords_pdf.index(None)
            except ValueError: # All assigned
                pass # next_unassigned_idx remains -1
            status_msg = f"Column {idx_to_update + 1} positioned. "
            self.status_label.config(text=status_msg + (f"Click to position column {next_unassigned_idx + 1}." if next_unassigned_idx != -1 else "All columns positioned."))
            self.active_coord_to_set_idx = None # Reset specific "Move" selection after any click
            
            self._draw_markers() 
            if self.is_text_preview_active: # Update preview if active
                self._update_text_preview()
    
    def on_marker_press(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        col_idx = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    col_idx = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        if col_idx == -1: return # Not a marker we are interested in

        self._drag_data["item"] = item_id
        self._drag_data["col_idx"] = col_idx
        self._drag_data["x"] = self.canvas.canvasx(event.x)
        self._drag_data["y"] = self.canvas.canvasy(event.y)
        self.active_coord_to_set_idx = None # Cancel click-to-set mode

    def on_marker_motion(self, event):
        if not self._drag_data["item"]:
            return

        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        
        dx = current_x - self._drag_data["x"]
        dy = current_y - self._drag_data["y"]

        self.canvas.move(self._drag_data["item"], dx, dy)

        self._drag_data["x"] = current_x
        self._drag_data["y"] = current_y

        # Update PDF coordinates
        marker_coords_canvas = self.canvas.coords(self._drag_data["item"]) # x1, y1, x2, y2
        # Center of the oval marker
        new_canvas_center_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
        new_canvas_center_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        
        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_center_x, new_canvas_center_y)

        current_col_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_col_idx is not None and 0 <= current_col_idx < len(self.coords_pdf):
            self.coords_pdf[current_col_idx] = pdf_coords
            # self.coord_texts[current_col_idx].set(f"מיקום {current_col_idx+1}: ({pdf_coords[0]:.1f}, {pdf_coords[1]:.1f}) נק'")
            
            if self.is_text_preview_active:
                self._update_text_preview()

    def on_marker_release(self, event):
        if not self._drag_data["item"]:
            return
        # Final update after drag, ensuring the latest position is used
        # This is mostly redundant if on_marker_motion updates correctly, but good for safety
        marker_coords_canvas = self.canvas.coords(self._drag_data["item"])
        new_canvas_center_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
        new_canvas_center_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_center_x, new_canvas_center_y)

        current_col_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_col_idx is not None and 0 <= current_col_idx < len(self.coords_pdf):
            self.coords_pdf[current_col_idx] = pdf_coords
            # self.coord_texts[current_col_idx].set(f"מיקום {current_col_idx+1}: ({pdf_coords[0]:.1f}, {pdf_coords[1]:.1f}) נק'")
            if current_col_idx < len(self.col_status_vars):
                 self.col_status_vars[current_col_idx].set("✔")
            self.status_label.config(text=f"Column {current_col_idx + 1} position updated by dragging.")

        self._drag_data["item"] = None
        self._drag_data["col_idx"] = None
        
        if self.is_text_preview_active: # Ensure preview updates on drag release
            self._update_text_preview()

    def on_marker_double_click(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        col_idx = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    col_idx = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        
        if col_idx != -1 and 0 <= col_idx < len(self.is_rtl_vars):
            current_rtl_var = self.is_rtl_vars[col_idx]
            current_rtl_var.set(not current_rtl_var.get()) # Toggle the boolean variable
            # The trace on is_rtl_vars will call _on_font_change, which updates the preview.
            self.status_label.config(text=f"Column {col_idx + 1} direction changed to {'RTL' if current_rtl_var.get() else 'LTR'}.")

    def toggle_text_preview(self):
        if not self.pdf_doc:
            messagebox.showwarning("Warning", "Please load a PDF file first.")
            return
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            messagebox.showwarning("Warning", "Please load an Excel file with data first.")
            return
        
        # Check if at least one coordinate is set for the existing columns
        if not self.coords_pdf or not any(c is not None for c in self.coords_pdf):
            if self.num_excel_cols > 0:
                messagebox.showwarning("Warning", f"Please select a position for at least one column on the PDF first.")
            else: # Should not happen if Excel is loaded, but as a safeguard
                messagebox.showwarning("Warning", "Please define text fields (load Excel) and select positions.")
            return
        
        # Toggle the state
        new_preview_state = not self.is_text_preview_active
        self.is_text_preview_active = new_preview_state # Set it first
        
        # Then update button text and preview based on the new state
        # (Button text update for Show/Hide can be added here if desired)
        self._update_text_preview()

    def _update_text_preview(self):
        # Clear existing preview text items
        for item_id in self.preview_text_items:
            self.canvas.delete(item_id)
        self.preview_text_items.clear()
        if not self.is_text_preview_active or \
           not self.pdf_doc or self.excel_data_preview is None or self.excel_data_preview.empty or \
           not self.coords_pdf or self.num_excel_cols == 0:
            return

        current_row_idx = self.preview_row_index.get()
        if not (self.excel_data_preview is not None and \
                0 <= current_row_idx < self.excel_data_preview.shape[0]):
            # print(f"Preview row index {current_row_idx} is out of bounds.") # Debug
            return # Invalid row index for preview
        try:
            font_family = self.font_family_var.get()
            font_size_from_input = self.font_size_var.get()
            if font_size_from_input <= 0: return # Invalid font size

            # Adjust base font size for Tkinter preview if it tends to look larger, then scale with zoom
            current_zoom = self.current_zoom_factor.get()
            adjusted_base_preview_size = font_size_from_input * TKINTER_FONT_SCALE_FACTOR
            preview_font_size = max(1, int(adjusted_base_preview_size * current_zoom))

            try:
                current_tk_font = tkFont.Font(family=font_family, size=preview_font_size)
            except tk.TclError as e: # Fallback if Tkinter can't create the font by name
                print(f"Error loading font '{font_family}' for Tkinter preview: {e}. Falling back to Arial.")
                current_tk_font = tkFont.Font(family="Arial", size=max(1, int(font_size_from_input * current_zoom))) # Fallback uses unscaled base
                # Consider applying TKINTER_FONT_SCALE_FACTOR to fallback as well for consistency:
                # current_tk_font = tkFont.Font(family="Arial", size=preview_font_size)
            for i in range(self.num_excel_cols):
                if i < len(self.coords_pdf) and self.coords_pdf[i] and \
                   i < len(self.is_rtl_vars) and i < self.excel_data_preview.shape[1]:
                    
                    val_preview = str(self.excel_data_preview.iloc[current_row_idx, i]) if pd.notna(self.excel_data_preview.iloc[current_row_idx, i]) else ""
                    # For Tkinter canvas preview, pass the logical string.
                    text_for_preview = val_preview 
                    
                    pdf_coord = self.coords_pdf[i]
                    is_rtl_current = self.is_rtl_vars[i].get()
                else:
                    continue # Skip if data for this column is incomplete

                canvas_coords = self._pdf_coords_to_canvas_coords(pdf_coord)
                if canvas_coords:
                    anchor_val = tk.SE if is_rtl_current else tk.SW
                    if current_tk_font:
                        item_id = self.canvas.create_text(canvas_coords[0], canvas_coords[1], text=text_for_preview,
                                                         font=current_tk_font, anchor=anchor_val, fill="purple", tags="preview_text_item")
                        self.preview_text_items.append(item_id)
                    else:
                        # Should not happen if fallback is in place
                        print("Error: No font object available for preview.")
        except Exception as e:
            print(f"Error updating text preview: {e}") # Log error, don't crash

    def _insert_text_on_pdf_page(self, page, text_value, pdf_coord_tuple, font_family_name, font_file_path, font_size_pt, is_rtl, fitz_font_object):
        """Helper function to insert text onto a PDF page."""
        if pdf_coord_tuple is None:
            return

        bidi_val = get_display(text_value, base_dir='R' if is_rtl else 'L')
        text_width_pt = fitz_font_object.text_length(bidi_val, fontsize=font_size_pt)

        insertion_point_x_pt = pdf_coord_tuple[0]
        # PyMuPDF's insert_text uses y from top of page.
        # self.coords_pdf stores y from bottom of page.
        insertion_point_y_pt = (self.pdf_page_height_pt - pdf_coord_tuple[1]) - Y_OFFSET_PDF_OUTPUT

        if is_rtl:
            insertion_point_x_pt -= text_width_pt

        page.insert_text((insertion_point_x_pt, insertion_point_y_pt),
                           bidi_val,
                           fontname=font_family_name,
                           fontfile=font_file_path,
                           fontsize=font_size_pt,
                           color=DEFAULT_PDF_TEXT_COLOR,
                           rotate=page.rotation)

    def generate_output_pdfs(self):
        if not self.pdf_path.get() or not self.excel_path.get() or not self.output_dir.get():
            messagebox.showerror("Error", "Please ensure PDF template, Excel file, and Output folder are selected.")
            return

        if not self.coords_pdf or not all(c is not None for c in self.coords_pdf):
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        try:
            df = pd.read_excel(self.excel_path.get(), header=None)
            if df.shape[1] != self.num_excel_cols: # Consistency check
                messagebox.showerror("Error", "The number of columns in the Excel file has changed since initial load. Please reload.")
                return

            font_family_selected = self.font_family_var.get()
            font_size = self.font_size_var.get()

            if not font_family_selected: # Should be caught by combobox default, but good check
                messagebox.showerror("Error", "Please select a font family.")
                return
            if font_size <= 0:
                messagebox.showerror("Error", "Font size must be positive.")
                return

            try:
                font_path = fm.findfont(font_family_selected)
            except Exception as e: # More general exception if findfont fails unexpectedly
                messagebox.showerror("Font File Error", f"Could not find the font file for '{font_family_selected}'.\nTry selecting a different font.\nError: {e}")
                self.status_label.config(text=f"Error: Font file not found for {font_family_selected}")
                return

            # Load font once for metrics and use in insert_text
            try:
                fitz_font = fitz.Font(fontname=font_family_selected, fontfile=font_path)
            except Exception as e:
                messagebox.showerror("Font Load Error", f"Could not load the font '{font_family_selected}' from path '{font_path}'.\n{e}")
                return

            self.status_label.config(text="Processing files...")
            self.master.update_idletasks() # Update GUI
            
            num_files_generated = 0 # Initialize counter for generated files
            for index, row in df.iterrows():
                doc_copy = fitz.open(self.pdf_path.get())
                page_to_modify = doc_copy.load_page(0)

                for i in range(self.num_excel_cols):
                    if i >= row.size or i >= len(self.coords_pdf) or self.coords_pdf[i] is None or i >= len(self.is_rtl_vars):
                        continue # Skip if data for this column is missing or not configured

                    val = str(row.iloc[i]) if pd.notna(row.iloc[i]) else ""
                    is_rtl_output = self.is_rtl_vars[i].get()
                    current_coord_pdf = self.coords_pdf[i]

                    self._insert_text_on_pdf_page(page_to_modify,
                                                  val,
                                                  current_coord_pdf,
                                                  font_family_selected,
                                                  font_path,
                                                  font_size,
                                                  is_rtl_output,
                                                  fitz_font)

                output_filename = os.path.join(self.output_dir.get(), f"output_pdf_{index + 1}.pdf")
                doc_copy.save(output_filename)
                doc_copy.close()
                num_files_generated += 1

            self.status_label.config(text=f"Finished generating {num_files_generated} PDF files in: {self.output_dir.get()}")
            messagebox.showinfo("Success", f"{num_files_generated} PDF files generated successfully!")

        except Exception as e:
            self.status_label.config(text="Error during file generation.")
            messagebox.showerror("Processing Error", str(e))

    def generate_single_preview_pdf(self):
        if not self.pdf_path.get():
            messagebox.showerror("Error", "Please load a PDF template file first.")
            return
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            messagebox.showerror("Error", "Please load an Excel file with data first.")
            return
        if not self.output_dir.get(): # Need an output dir for the save dialog's initial dir
            messagebox.showerror("Error", "Please select an output folder first (to save the current file).")
            return
        if not self.coords_pdf or not all(c is not None for c in self.coords_pdf):
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        current_row_idx = self.preview_row_index.get()
        if not (0 <= current_row_idx < self.excel_data_preview.shape[0]):
            messagebox.showerror("Error", "Invalid row selected for preview.")
            return

        font_family_selected = self.font_family_var.get()
        font_size = self.font_size_var.get()

        if not font_family_selected:
            messagebox.showerror("Error", "Please select a font family.")
            return
        if font_size <= 0:
            messagebox.showerror("Error", "Font size must be positive.")
            return

        try:
            font_path = fm.findfont(font_family_selected)
            fitz_font = fitz.Font(fontname=font_family_selected, fontfile=font_path)
        except Exception as e:
            messagebox.showerror("Font Error", f"Could not load the font '{font_family_selected}'.\n{e}")
            return

        output_filepath = filedialog.asksaveasfilename(
            initialdir=self.output_dir.get(),
            title="Save current PDF As",
            defaultextension=".pdf",
            filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )

        if not output_filepath: # User cancelled save dialog
            return

        try:
            self.status_label.config(text="Generating current PDF...")
            self.master.update_idletasks()

            row_data = self.excel_data_preview.iloc[current_row_idx]
            
            doc_copy = fitz.open(self.pdf_path.get())
            page_to_modify = doc_copy.load_page(0)

            for i in range(self.num_excel_cols):
                if i >= row_data.size or i >= len(self.coords_pdf) or self.coords_pdf[i] is None or i >= len(self.is_rtl_vars):
                    continue

                val = str(row_data.iloc[i]) if pd.notna(row_data.iloc[i]) else ""
                is_rtl_output = self.is_rtl_vars[i].get()
                current_coord_pdf = self.coords_pdf[i]

                self._insert_text_on_pdf_page(page_to_modify,
                                              val,
                                              current_coord_pdf,
                                              font_family_selected,
                                              font_path,
                                              font_size,
                                              is_rtl_output,
                                              fitz_font)

            doc_copy.save(output_filepath)
            doc_copy.close()
            self.status_label.config(text=f"current PDF saved to: {output_filepath}")
            messagebox.showinfo("Success", f"current PDF saved successfully!")
        except Exception as e:
            self.status_label.config(text="Error generating current PDF.")
            messagebox.showerror("Error Generating current PDF", str(e))

if __name__ == "__main__":
    root = tk.Tk()
    default_font = tkFont.nametofont("TkDefaultFont")
    default_font.configure(family="Arial", size=10)
    root.option_add("*Font", default_font)

    app = PDFBatchApp(root)
    root.mainloop()