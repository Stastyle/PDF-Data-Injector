# PDF Data Injector

This application allows users to dynamically inject data from an Excel spreadsheet into a PDF template. It provides a graphical user interface (GUI) to visually position text fields onto a preview of the PDF, and then batch-generates multiple personalized PDF documents, each populated with data from a row in the Excel file.

## Key Features

* **PDF Template Loading:** Load an existing PDF file to be used as a template (processes the first page).
* **Excel Data Import:** Import data from Excel files (`.xlsx`, `.xls`). Each column in the Excel sheet represents a distinct text field to be injected.
* **Visual Field Placement:**
    * Interactive PDF preview.
    * Click on the preview to define the coordinates for text fields.
    * Drag-and-drop colored markers for precise positioning of each field.
    * A sidebar lists all columns (fields) from the Excel file, each with a "Move" button for re-positioning.
* **Live Text Preview:**
    * Displays sample text from the selected Excel row directly onto the PDF preview.
    * Automatically updates the preview when font, font size, or Right-to-Left (RTL) settings are changed.
* **Font Configuration:**
    * Select font family from system-installed fonts.
    * Specify font size.
* **Right-to-Left (RTL) Text Support:**
    * Individually configure each text field for RTL languages (e.g., Hebrew, Arabic).
    * Toggle RTL status via a checkbox in the sidebar or by double-clicking the corresponding marker on the PDF preview.
* **Preview Navigation & Control:**
    * **Zoom:** Zoom in and out of the PDF preview using dedicated buttons or the mouse wheel.
    * **Pan:** Pan the PDF preview by clicking and dragging (left mouse button) on the canvas background.
    * **Excel Row Navigation:** Use "↑" (previous row) and "↓" (next row) buttons to cycle through Excel data for preview.
* **PDF Generation:**
    * **"Generate current PDF":** Create a single PDF file based on the currently previewed Excel row data. Prompts for a save location.
    * **"Generate PDF Files":** Batch-create PDF files for all rows in the Excel sheet. Files are saved in the designated output folder.
* **Output Directory Selection:** Choose a folder where the generated PDF files will be saved.
* **Status Bar:** Provides user feedback and instructions at the bottom of the application window.

## Prerequisites and Installation

1.  **Python:** Ensure Python 3.6 or higher is installed.
2.  **Python Libraries:** Install the required Python libraries. It's recommended to use a virtual environment.

    ```bash
    pip install pandas PyMuPDF arabic_reshaper python-bidi matplotlib
    ```

    * `pandas`: For reading and processing Excel files.
    * `PyMuPDF` (fitz): For PDF manipulation (reading, writing, image rendering).
    * `arabic_reshaper`: For shaping characters in RTL languages like Arabic.
    * `python-bidi`: For applying the Bidirectional Algorithm for RTL text.
    * `matplotlib`: For finding system font file paths.

## Usage Instructions

1.  **Launch the Application:**
    Run the Python script from your terminal:
    ```bash
    python PDFDataInjector.py
    ```

2.  **Load Files:**
    * **Load PDF Template:** Click the "Select PDF" button and choose your PDF template file. The preview will update.
    * **Load Excel Data File:** Click the "Select Excel" button and choose your data file. The number of columns in the Excel file will determine the number of available text fields. The right-hand sidebar will populate accordingly.
    * **Select Output Folder:** Click the "Select Folder" button and choose the directory where generated PDFs will be saved.

3.  **Configure Font:**
    * Select the desired **Font Family** from the dropdown list.
    * Enter the desired **Size** in the font size field.

4.  **Position Text Fields:**
    * For each "Column" (text field) listed in the right-hand sidebar:
        * Click the **"Move"** button next to the column you wish to position.
        * Then, click on the PDF preview image at the desired location for this field. A colored marker will appear.
        * Alternatively, without clicking "Move", you can click directly on the PDF preview to sequentially place the next unassigned field.
    * You can drag any existing colored marker on the preview to adjust its position.
    * For each field, you can check/uncheck the **"RTL"** checkbox in the sidebar to set text direction. You can also toggle the RTL status by double-clicking the corresponding marker on the PDF.
    * A "✔" status indicates the field is positioned; "✖" indicates it's not yet positioned.

5.  **Preview and Navigate:**
    * Use the **"+"** and **"-"** buttons or the mouse wheel to **Zoom** the PDF preview.
    * Click and drag (with the left mouse button) on the PDF background to **Pan** the view.
    * Use the **"↑"** (Previous Row) and **"↓"** (Next Row) buttons to cycle through data from your Excel file. The text preview on the PDF will update.
    * Click the **"Show/Hide Preview"** button to toggle the visibility of the live text on the PDF.

6.  **Generate PDFs:**
    * **"Generate current PDF":** After positioning all fields and selecting a desired data row from Excel, click this button. You will be prompted to choose a name and location to save this single PDF.
    * **"Generate PDF Files":** Click this button to create PDF files for *all* rows in your Excel file. The files will be saved in the selected output folder, typically named `output_pdf_{row_number}.pdf`.

## Important Notes

* **PDF Template:** The application currently uses only the first page of the selected PDF template.
* **Excel File:**
    * Data is read from the first sheet of the Excel file.
    * It assumes there is no header row, and data starts from the first row.
    * Each column in the Excel file corresponds to a separate text field.
* **Fonts:**
    * The application relies on the selected fonts being properly installed on your operating system and accessible. `matplotlib.font_manager` is used to locate the font file path.
    * Correct rendering of text (especially for RTL languages) depends on the font's support for the required characters.
* **Default RTL:** When an Excel file is loaded, new fields default to RTL (Right-to-Left) being checked.

## File Structure (Input/Output)

* **Input:**
    * A PDF file to serve as the template (effectively single-page usage).
    * An Excel file (`.xlsx` or `.xls`) where each row represents an individual document and each column represents a data field.
* **Output:**
    * Multiple PDF files in the specified output directory, each populated with data from a corresponding row in the Excel file.

---

Author: stas.meirovich@gmail.com
License: [GNU General Public License v3.0]